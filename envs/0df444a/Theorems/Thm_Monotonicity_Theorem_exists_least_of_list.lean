-- Prove2me | Theorems.Thm_Monotonicity_Theorem_exists_least_of_list
-- name    : Monotonicity_Theorem.exists_least_of_list
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:25:28.79727+00:00
-- url     : https://prove2.me/theorems/d4add2a3-d45d-4bba-8197-2743d1390f0b
-- title:
--   Nonempty coordinate lists have a least element
-- statement:
--   Every nonempty list of coordinates has a least element for the dense order: some listed m with every listed r above m or equal to it. This is the entry point to the minimum-preimage construction of the Lemma 1 finite-fiber case.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber step; supporting extrema lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.exists_least_of_list {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (L : List R) (hNe : L ≠ []) :
    exists m : R, m ∈ L /\ forall r : R, r ∈ L -> (D.lt m r \/ m = r) := by sorry
