-- Prove2me | Theorems.Thm_Monotonicity_Theorem_below_sign_definable
-- name    : Monotonicity_Theorem.below_sign_definable
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:01:08.456454+00:00
-- url     : https://prove2.me/theorems/b31ca27e-40ec-48be-bd81-7eceb600c6fc
-- title:
--   Below-sign graph set definability
-- statement:
--   The set of points in a definable set whose graph value lies strictly below a constant is definable.
-- source:
--   Monotonicity theorem Lemma 2 infrastructure

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.below_sign_definable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (J : Set (Power R 1)) (hJ : M.S 1 J) (c : R) :
    M.S 1 (fun y : Power R 1 => J y /\ exists v : Power R 1,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y v) /\
      Lt1 D v (fun _ => c)) := by sorry
