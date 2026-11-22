-- Prove2me | Theorems.Thm_Monotonicity_Theorem_exists_greatest_of_list
-- name    : Monotonicity_Theorem.exists_greatest_of_list
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:03:20.581243+00:00
-- url     : https://prove2.me/theorems/7acda774-0753-474f-8119-a5c3a61596ff
-- title:
--   Greatest element of a nonempty list
-- statement:
--   Every nonempty list over a dense linear order without endpoints has a greatest element.
-- source:
--   Monotonicity theorem Lemma 2 infrastructure

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.exists_greatest_of_list {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (L : List R) (hNe : L ≠ []) :
    exists M : R, M ∈ L /\ forall r : R, r ∈ L -> (D.lt r M \/ r = M) := by sorry
