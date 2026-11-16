-- Prove2me | Theorems.Thm_Kyprianou_Ch06_iIndepFun_of_delete_constant
-- name    : Kyprianou.Ch06.iIndepFun_of_delete_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:28:53.87903+00:00
-- url     : https://prove2.me/theorems/6929d38d-1ce2-4003-add4-6be1a0f9d87b
-- title:
--   Reinserting one deterministic zero coordinate preserves finite-dimensional independence
-- statement:
--   Suppose the non-distinguished coordinates of a random-variable family satisfy all finite rectangle factorisation identities and the distinguished variable is identically zero. Under a unit-mass measure the entire family is independent. This is a reusable conditional extension lemma for deleting and reinserting zero-length increments of monotone time grids.
-- source:
--   General finite-dimensional probability consequence from Mathlib iIndepFun_iff_measure_inter_preimage_eq_mul. Supporting source-faithful Chapter 6 weak-grid bridge.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem Kyprianou.Ch06.iIndepFun_of_delete_constant
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (f : ι → Ω → Real) (k : ι)
    (hconst : f k = fun _ => 0)
    (hrest : ∀ (S : Finset ι), k ∉ S →
      ∀ (A : ι → Set Real), (∀ i ∈ S, MeasurableSet (A i)) →
      P (⋂ i ∈ S, f i ⁻¹' A i) =
        ∏ i ∈ S, P (f i ⁻¹' A i)) :
    ProbabilityTheory.iIndepFun f P := by sorry
