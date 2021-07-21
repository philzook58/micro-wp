open Core_kernel
open Bap.Std

include Self()
let _ : (unit, Bap_main.error) Stdlib.result = Bap_main.init ()

let myfile = "/home/philip/Documents/ocaml/cribes-foolin/micro-wp/a.out"
let proj = Project.create (Project.Input.file ~loader:"llvm" ~filename:myfile) |> Or_error.ok_exn
let prog = Project.program proj
(* let () = Term.enum sub_t prog |> Seq.iter ~f:(fun s -> Printf.printf "%s\n" (Term.name s))
*)
let main = Term.enum sub_t prog |> Seq.find ~f:(fun s -> String.equal (Term.name s) "@main") |> Option.value_exn
let () = Printf.printf "%s\n" (Sub.to_string main)
let all_vars = Wp.all_vars main
let blks = Term.enum blk_t main
let () = Seq.iter blks ~f:(fun blk ->
  Format.printf "Block :\n%a\n%!" Blk.pp blk;
  let pre = Wp.wp_block blk all_vars in
  Printf.printf "Z3 Expr:\n%s\n%!" (Z3.Expr.to_string pre)
  )
(* Term.enum sub_t Term.find blk_t sub *)
Program.lookup blk_t prog (Theory.Label.for_addr (Bitvec.int 0x400) )
(*
let ssa_sub = Sub.ssa main
let () = Printf.printf "%s\n" (Sub.to_string ssa_sub)
let liveness_sol = Sub.compute_liveness ssa_sub
let () = Seq.iter (Graphlib.Std.Solution.enum liveness_sol) ~f:(fun (tid, varset) -> 
  Format.printf "%a \t %s \n" Tid.pp tid (Var.Set.to_list varset |> List.map ~f:Var.name |> String.concat ~sep:" ")
  )
let blks = Term.enum blk_t ssa_sub
let entry_live = Seq.map blks ~f:(fun b ->
  let exit_live = Graphlib.Std.Solution.get liveness_sol (Term.tid b) in
  let fvs = Blk.free_vars b in
  let def_vars = Seq.map ~f:Def.lhs (Term.enum def_t b) |> Seq.to_list |> Var.Set.of_list in
  (Term.tid b, Var.Set.diff (Var.Set.union exit_live fvs) def_vars)
)
let () = Seq.iter entry_live  ~f:(fun (tid, varset) -> 
  Format.printf "%a \t %s \n" Tid.pp tid (Var.Set.to_list varset |> List.map ~f:Var.name |> String.concat ~sep:" ")
  )
  *)

(*

Am I doing this wrong.
Maybe no ssa. Just have every block carry every variable.
And then do wp on predicate (after jumps?). This is what the paper actually describes.
We could do liveness and 

let ssa_sub = Sub.ssa sub in
let liveness_sol = Sub.compute_liveness ssa_sub in
let exit_live_b = Solution.get liveness_sol (Term.tid b)
let intro_live_b = exit_live + Blk.free_vars b - defined b 
(* Or is SSA going to be kind with phi nodes? 
I need to just look at some
*)
*)



(*
open Core_kernel
open Bap.Std

include Self()
let _ : (unit, Bap_main.error) Stdlib.result = Bap_main.init ()

let myfile = "/home/philip/Documents/ocaml/cribes-foolin/micro-wp/a.out"
let proj = Project.create (Project.Input.file ~loader:"llvm" ~filename:myfile) |> Or_error.ok_exn
let prog = Project.program proj

(* Hmm. Maybe only works if we give blk address on the nose *)
let (Some blk) = Program.lookup blk_t prog (Tid.for_addr (Word.of_int ~width:64 0x112d) )
let () = Format.printf "%a\n" Blk.pp blk
let (Some addr) = (Term.get_attr blk address)
let () = Format.printf "%a\n" Addr.pp addr
let () = Format.printf "%a\n" Sexp.pp (Term.attrs blk |> Dict.sexp_of_t) 
(* Yes this basicaslly works.
But now I have to back prop the different gotos? So I need to go from the tid of the jmps to
addresses?

*)

(*
Do I want this as an http service like I said?
*)





*)