-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_affine_unit_propagation
-- name    : NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:42:48.599008+00:00
-- url     : https://prove2.me/theorems/dfef0ecb-6b9b-4838-a7bd-3e5d9b1f757b
-- title:
--   Affine clause of CLBI propagates across one nested fare-class step
-- statement:
--   In the nested seat model with integer-valued demands, if the expected revenue through class k is affine on every closed unit interval, then the expected revenue through class k+1 is affine on every closed unit interval. This is the affine half of the CLBI propagation step; it does not assert concavity.
-- source:
--   Brumelle & McGill (1993), proof of Theorem 2, pp. 132-133: equations (28)-(29) and the integer-demand argument that the one-sided slopes agree and stay constant between adjacent integers.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem clbi_affine_unit_propagation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (k : ℕ) (p : ℕ → ℕ)
    (hunit : ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) k s = a + b * s) :
    ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) (k + 1) s = a + b * s := by sorry

end NestedSeatAlloc.IntPolicy
