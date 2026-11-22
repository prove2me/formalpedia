-- Prove2me | Theorems.Thm_Monotonicity_Theorem_above_sign_definable
-- name    : Monotonicity_Theorem.above_sign_definable
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:01:04.592108+00:00
-- url     : https://prove2.me/theorems/2263a86c-5477-4fe1-b0f1-3781a7e5bd6f
-- title:
--   Above-sign graph set definability
-- statement:
--   The set of points in a definable set whose graph value lies strictly above a constant is definable.
-- source:
--   Monotonicity theorem Lemma 2 infrastructure

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.above_sign_definable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (J : Set (Power R 1)) (hJ : M.S 1 J) (c : R) :
    M.S 1 (fun y : Power R 1 => J y /\ exists v : Power R 1,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y v) /\
      Lt1 D (fun _ => c) v) := by sorry
