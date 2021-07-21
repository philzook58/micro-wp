open Core_kernel
open Bap.Std

module Expr = Z3.Expr
module Arith = Z3.Arithmetic
module BV = Z3.BitVector
module Bool = Z3.Boolean
module Z3Array = Z3.Z3Array
(*

module FuncDecl = Z3.FuncDecl
module Solver = Z3.Solver
module Env = Environment
module Constr = Constraint
*)

module Constr = struct
  type z3_expr = Z3.Expr.expr
  type t = Z3.Expr.expr
end
(*
struct Ent
  type t = 
end
*)

(* Could make this a ref, pass functionally throughout user Reader.
    
*)
let ctx = Z3.mk_context []

let mk_z3_sort (ctx : Z3.context) (typ : Type.t) = 
  match typ with
  | Type.Imm size -> Z3.BitVector.mk_sort ctx size
  | Type.Mem (i_size, w_size) ->
    let i_sort = Z3.BitVector.mk_sort ctx (Size.in_bits i_size) in
    let w_sort = Z3.BitVector.mk_sort ctx (Size.in_bits w_size) in
    Z3.Z3Array.mk_sort ctx i_sort w_sort
  | Type.Unk ->
    failwith "mk_z3_expr: type is not representable by Type.t"


let mk_z3_expr (ctx : Z3.context) ~name:(name : string) ~typ:(typ : Type.t) : Constr.z3_expr =
  match typ with
  | Type.Imm size -> Z3.BitVector.mk_const_s ctx name size
  | Type.Mem (i_size, w_size) ->
    let i_sort = Z3.BitVector.mk_sort ctx (Size.in_bits i_size) in
    let w_sort = Z3.BitVector.mk_sort ctx (Size.in_bits w_size) in
    Z3.Z3Array.mk_const_s ctx name i_sort w_sort
  | Type.Unk ->
    failwith "mk_z3_expr: type is not representable by Type.t"

let mk_var ctx (var : Var.t) : Z3.Expr.expr =     
  let typ = Var.typ var in
  let full_name = Var.name var ^ (string_of_int (Var.index var)) in
  mk_z3_expr ctx ~name:full_name ~typ:typ

let z3_expr_zero (ctx : Z3.context) (size : int) : Constr.z3_expr = BV.mk_numeral ctx "0" size
let z3_expr_one (ctx : Z3.context) (size : int) : Constr.z3_expr = BV.mk_numeral ctx "1" size

let bv_to_bool (bv : Constr.z3_expr) (ctx : Z3.context) (width : int) : Constr.z3_expr =
  let zero = z3_expr_zero ctx width in
  Bool.mk_not ctx (Bool.mk_eq ctx bv zero)

let binop (ctx : Z3.context) (b : binop) :
  Constr.z3_expr -> Constr.z3_expr -> Constr.z3_expr =
  let open Bap.Std.Bil.Types in
  let zero = z3_expr_zero ctx 1 in
  let one = z3_expr_one ctx 1 in
  match b with
  | PLUS -> BV.mk_add ctx
  | MINUS -> BV.mk_sub ctx
  | TIMES -> BV.mk_mul ctx
  | DIVIDE -> BV.mk_udiv ctx
  | SDIVIDE -> BV.mk_sdiv ctx
  | MOD -> BV.mk_urem ctx
  | SMOD -> BV.mk_smod ctx
  | LSHIFT -> BV.mk_shl ctx
  | RSHIFT -> BV.mk_lshr ctx
  | ARSHIFT -> BV.mk_ashr ctx
  | AND -> BV.mk_and ctx
  | OR -> BV.mk_or ctx
  | XOR -> BV.mk_xor ctx
  | EQ -> fun x y -> Bool.mk_ite ctx (Bool.mk_eq ctx x y) one zero
  | NEQ -> fun x y -> Bool.mk_ite ctx (Bool.mk_eq ctx x y) zero one
  | LT -> fun x y -> Bool.mk_ite ctx (BV.mk_ult ctx x y) one zero
  | LE -> fun x y -> Bool.mk_ite ctx (BV.mk_ule ctx x y) one zero
  | SLT -> fun x y -> Bool.mk_ite ctx (BV.mk_slt ctx x y) one zero
  | SLE -> fun x y -> Bool.mk_ite ctx (BV.mk_sle ctx x y) one zero

let unop (ctx : Z3.context) (u : unop) : Constr.z3_expr -> Constr.z3_expr =
  let open Bap.Std.Bil.Types in
  match u with
  | NEG -> BV.mk_neg ctx
  | NOT -> BV.mk_not ctx

let cast (ctx : Z3.context) (cst : cast) (i : int) (x : Constr.z3_expr) : Constr.z3_expr =
  assert (i > 0);
  let size = x |> Expr.get_sort |> BV.get_size in
  let open Bap.Std.Bil.Types in
  match cst with
  | UNSIGNED -> BV.mk_zero_ext ctx (i - size) x
  | SIGNED -> BV.mk_sign_ext ctx (i - size) x
  | HIGH -> BV.mk_extract ctx (size - 1) (size - i) x
  | LOW -> BV.mk_extract ctx (i - 1) 0 x

let load_z3_mem (ctx : Z3.context) ~word_size:word_size ~mem:(mem : Constr.z3_expr)
    ~addr:(addr : Constr.z3_expr) (endian : Bap.Std.endian) : Constr.z3_expr =
  assert (Z3Array.is_array mem && mem |> Expr.get_sort
                                  |> Z3Array.get_range
                                  |> Z3.Sort.get_sort_kind
                                  |> (function
                                      | Z3enums.BV_SORT -> true
                                      |_ -> false));
  let m_size = mem |> Expr.get_sort |> Z3Array.get_range |> BV.get_size in
  let addr_size = addr |> Expr.get_sort |> BV.get_size in
  let nums_to_read = word_size / m_size in
  assert (nums_to_read > 0);
  let rec read_list n addr reads =
    if n = 0 then reads
    else
      (* TODO: handle overflow *)
      let addr' = BV.mk_add ctx addr (z3_expr_one ctx addr_size) in
      read_list (n-1) addr' (Z3Array.mk_select ctx mem addr :: reads)
  in
  let read = read_list nums_to_read addr [] in
  let read_sorted =
    match endian with
    | BigEndian -> List.rev read
    | LittleEndian -> read
  in
  List.reduce_exn read_sorted ~f:(BV.mk_concat ctx)

let store_z3_mem (ctx : Z3.context) ~word_size:word_size
    ~mem:(mem : Constr.z3_expr) ~addr:(addr : Constr.z3_expr) ~content:(e : Constr.z3_expr)
    (endian : Bap.Std.endian) : Constr.z3_expr =
  let m_size = mem |> Expr.get_sort |> Z3Array.get_range |> BV.get_size in
  let addr_size = addr |> Expr.get_sort |> BV.get_size in
  let nums_to_write = word_size / m_size in
  let first_loc, next_loc =
    match endian with
    | BigEndian -> word_size - m_size, fun l -> l - m_size
    | LittleEndian -> 0, fun l -> l + m_size
  in
  assert (nums_to_write > 0);
  let rec store n loc addr mem =
    if n = 0 then mem
    else
      begin
        (* TODO: handle overflow *)
        let e_chunk_n = BV.mk_extract ctx (loc + m_size - 1) loc e in
        let mem' = Z3Array.mk_store ctx mem addr e_chunk_n in
        let addr' = BV.mk_add ctx addr (z3_expr_one ctx addr_size) in
        store (n-1) (next_loc loc) addr' mem'
      end
  in
  store nums_to_write first_loc addr mem

let word_to_z3 (ctx : Z3.context) (w : Word.t) : Constr.z3_expr =
  let fmt = Format.str_formatter in
  Word.pp_dec fmt w;
  let s = Format.flush_str_formatter () in
  BV.mk_numeral ctx s (Word.bitwidth w)

let exp_to_z3 (exp : Exp.t) (ctx : Z3.context) : Z3.Expr.expr  =
let open Bap.Std.Bil.Types in
let rec exp_to_z3_body exp : Z3.Expr.expr =
  match exp with
  | Load (mem, addr, endian, size) ->
    let mem_val = exp_to_z3_body mem in
    let addr_val = exp_to_z3_body addr in
    load_z3_mem ctx ~word_size:(Size.in_bits size) ~mem:mem_val ~addr:addr_val endian
  | Store (mem, addr, exp, endian, size) ->
    let mem_val = exp_to_z3_body mem in
    let addr_val = exp_to_z3_body addr in
    let exp_val = exp_to_z3_body exp in
    store_z3_mem ctx ~word_size:(Size.in_bits size)
      ~mem:mem_val ~addr:addr_val ~content:exp_val endian
  | BinOp (bop, x, y) ->
    let get_size v = v |> Expr.get_sort |> BV.get_size in
    let x_val = exp_to_z3_body x in
    let y_val = exp_to_z3_body y in
    (* In x86 decoding, it is possible to scale the address with a 2-bitwidth shift
       of 0, 1, 2, or 3. However, Z3 requires requires the operands of a bit shift
       to be of the same bitwidth. Here, we pad the operand with the smaller
       bitwidth to match the bitwidth of the other operand. *)
    let x_val, y_val =
      match bop with
      | LSHIFT | RSHIFT | ARSHIFT ->
        let x_size = get_size x_val in
        let y_size = get_size y_val in
        if x_size > y_size then
          x_val, BV.mk_zero_ext ctx (x_size - y_size) y_val
        else if y_size > x_size then
          BV.mk_zero_ext ctx (y_size - x_size) x_val, y_val
        else
          x_val, y_val
      | _ -> x_val, y_val
    in
    assert (get_size x_val = get_size y_val);
    binop ctx bop x_val y_val
  | UnOp (u, x) ->
    let x_val = exp_to_z3_body x in
    unop ctx u x_val
  | Var v -> mk_var ctx v
  | Bil.Types.Int w ->
    word_to_z3 ctx w
  | Cast (cst, i, x) ->
    let x_val = exp_to_z3_body x in
    cast ctx cst i x_val
  | Let (v, exp, body) ->
    let exp_val = exp_to_z3_body exp in
    let v = mk_var ctx v in
    let z3_expr = exp_to_z3_body body in
    Z3.Expr.substitute z3_expr [v] [exp_val]
  | Unknown (str, typ) -> mk_z3_expr ctx ~name:("unknown_" ^ str) ~typ (* This needs to be fresh? *)
  | Ite (cond, yes, no) ->
    let cond_val = exp_to_z3_body cond in
    let cond_size = BV.get_size (Expr.get_sort cond_val) in
    let yes_val = exp_to_z3_body yes in
    let no_val = exp_to_z3_body no in
    Bool.mk_ite ctx (bv_to_bool cond_val ctx cond_size) yes_val no_val
  | Extract (high, low, exp) ->
    let exp_val = exp_to_z3_body exp in
    BV.mk_extract ctx high low exp_val
  | Concat (w1, w2) ->
    let w1_val = exp_to_z3_body w1 in
    let w2_val = exp_to_z3_body w2 in
    BV.mk_concat ctx w1_val w2_val
in
exp_to_z3_body exp

let wp_def (def : Def.t) (post : Constr.t) : Constr.t =
  let var = Def.lhs def in
  let rhs = Def.rhs def in
  let rhs_exp = exp_to_z3 rhs ctx in
  let z3_var = mk_var ctx var in
  let post = Z3.Expr.substitute post [z3_var] [rhs_exp] in
  post


let pred_of_blk (blk : Blk.t) (typs : Type.t list) : Expr.expr list -> Expr.expr = 
  let block_decl = Z3.FuncDecl.mk_func_decl_s ctx
    (Tid.to_string (Term.tid blk))
    (List.map ~f:(mk_z3_sort ctx) typs)
    (Bool.mk_sort ctx) in
  fun z3_vars -> Z3.FuncDecl.apply block_decl z3_vars

(* FIXME: handle other architectures *)
(*
let increment_stack_ptr (post : Constr.t) (env : Env.t) : Constr.t * Env.t =
  let target = Env.get_target env in
  if Env.is_x86 target then
    begin
      let sp, env = Env.get_sp env |> Env.get_var env in
      let width = target |> Theory.Target.bits in
      let addr_size = target |> Theory.Target.code_addr_size in
      let addr_size = addr_size / Theory.Target.byte target in
      let ctx = Env.get_context env in
      let offset = BV.mk_numeral ctx (Int.to_string addr_size) width in
      let z3_off = BV.mk_add ctx sp offset in
      Constr.substitute_one post sp z3_off, env
    end
  else
    post, env


  let lookup_sub_handler (tid: Bap.Std.Tid.t) (env: Env.t) (post: Constr.t) =
    match Env.get_sub_handler env tid with
    | Some (Summary compute_func) -> compute_func env post tid
    | Some Inline -> !inline_func post env tid
    | None -> post, env

let indirect_spec_default : Env.indirect_spec =
    (* NOTE we keep around exp for that point in the future
      * when we can use it to determine the destination of the
      * indirect call. *)
    fun env post _exp has_return ->
    if has_return then increment_stack_ptr post env
    else post, env
*)
  let visit_call (call: Bap.Std.Call.t) (post : Constr.t) (all_vars) : Constr.t =
    let target = Call.target call in
    let return = Call.return call in
    match target, return with
    | Indirect t_exp, None -> post (*  This is function end?
    Env.get_indirect_handler env t_exp env post t_exp false *)
    | Direct t_tid, Some (Direct r_tid) ->
      (* I have not dealt with t_tid *)
      let block_decl = Z3.FuncDecl.mk_func_decl_s ctx
      (Tid.to_string r_tid)
      (List.map ~f:Expr.get_sort all_vars)
      (Bool.mk_sort ctx) in
      Z3.FuncDecl.apply block_decl all_vars
      (* let ret_pre = lookup_precond r_tid env post in
      lookup_sub_handler t_tid env ret_pre *)
    | _, _ -> failwith "other call not supported"
    (*
    | Indirect t_exp, Some (Direct r_tid) -> 
      (* let ret_pre = lookup_precond r_tid env post in
      Env.get_indirect_handler env t_exp env ret_pre t_exp true *)
    | Direct t_tid, Some (Indirect _) ->
      post
    | Indirect _, Some (Indirect _) ->
      post
    | Direct t_tid, None ->
      lookup_sub_handler t_tid env post

 *)



(* Determines the condition for taking a jump, and uses it to generate the jump
   expression's precondition based off of the postcondition and the
   precondition of the jump's target. *)
let conditional_jmp (jmp : Jmp.t) (target_pre : Constr.t)
   (post : Constr.t) : Constr.t  =
 let cond = Jmp.cond jmp in
 let cond_val = exp_to_z3 cond ctx in
 let cond_size = BV.get_size (Expr.get_sort cond_val) in
 let false_cond = Bool.mk_eq ctx cond_val (z3_expr_zero ctx cond_size) in
 let is_unconditional =
   match cond with
   | Bil.Types.Int w -> Word.is_one w
   | _ -> false
 in
  if is_unconditional then
     target_pre
  else
     (* I don't think the z3 horn solvers support ite, but they do support or. *)
     Bool.mk_or ctx [Bool.mk_and ctx [(Bool.mk_not ctx false_cond); target_pre] ;
       Bool.mk_and ctx [false_cond; post] ]
    (*  Constr.mk_ite jmp (Bool.mk_not ctx false_cond) target_pre post *)
 (* in
 (* If we add a PC variable, we should separate the befores and afters
    similarly to how we did in visit_def *)
 let vcs = hooks.verify_before @ hooks.verify_after in
 let assume = hooks.assume_before @ hooks.assume_after in
 let post = ite :: vcs in
 Constr.mk_clause assume post, env *)

let visit_jmp (all_vars : Z3.Expr.expr list) (post : Constr.t) (jmp : Jmp.t) : Constr.t =
   let target_pre =
     match Jmp.kind jmp with
     | Goto l ->
       begin
         match l with
         | Direct tid ->
           begin
             let block_decl = Z3.FuncDecl.mk_func_decl_s ctx
                (Tid.to_string tid)
                (List.map ~f:Expr.get_sort all_vars)
                (Bool.mk_sort ctx) in
             Z3.FuncDecl.apply block_decl all_vars
             (* match Env.get_precondition env tid with
             | Some pre -> pre, env
             (* We always hit this point when finish a loop unrolling *)
             | None ->
               error "Precondition for node %s not found!" (Tid.to_string tid);
               failwith ("Error in visit_jmp: \
                          The loop handler should have added the precondition for the node"); *)
           end
         | Indirect _ -> failwith "Making an indirect jump, Not supported\n%!"
       end
     | Call call -> visit_call call post all_vars (* Bool.mk_false ctx *) (* failwith "visit call unimplement" *) (* visit_call call post env *)
     | Ret l -> post
     | Int (i, tid) -> failwith "Interrupt Not Handled"
   in
   conditional_jmp jmp target_pre post


let wp_elt (all_vars) (elt : Blk.elt) (post : Constr.t)  : Constr.t =
  match elt with
  | `Def def -> wp_def def post
  | `Jmp jmp -> visit_jmp all_vars post jmp
  | `Phi _ ->
    failwith "We do not currently handle Phi nodes.\n%!"
(*
attempt at the CHC thing

let wp_block (blk : Blk.t) (all_vars : Var.t list) : Constr.t =
  let elts = Blk.elts ~rev:true blk in
  let typs = List.map ~f:Var.typ all_vars in
  let post = Bool.mk_true ctx in (* Should be global post I guess *)
  let z3_all_vars = List.map ~f:(mk_var ctx) all_vars in 
  let pre = Seq.fold elts ~init:post ~f:(fun post_elt elt -> wp_elt z3_all_vars elt post_elt) in
  let head = (pred_of_blk blk typs) z3_all_vars  in
  Bool.mk_implies ctx pre head 
*)
let wp_block (block_map : Constr.t Tid.Map.t) (blk : Blk.t) : Constr.t =
  let elts = Blk.elts ~rev:true blk in




let wp_sub (init_block_map : Constr.t Tid.Map.t) (sub : Sub.t) : Constr.t Tid.Map.t =
  let blks = Term.enum ~rev:true blk_t sub
  Seq.fold ~init:init_block_map ~f:(fun block_map blk ->
      let pre = wp_blk block_map blk in
      Tid.Map.update block_map pre
    )

let blk_defs blk =
  Term.enum def_t blk |>
  Seq.fold ~init:Var.Set.empty  ~f:(fun defs def ->
      Set.add defs (Def.lhs def))

let all_vars (sub : Sub.t) : Var.t list = 
  let fvs =  Sub.free_vars sub in
  let defvs = Var.Set.union_list (Seq.to_list (Seq.map ~f:blk_defs (Term.enum blk_t sub))) in 
  Var.Set.union fvs defvs |> Var.Set.to_list