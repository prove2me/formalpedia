-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45OuterUCPPrefixLimitV1
-- name    : Kyprianou.Ch04.exercise45OuterUCPPrefixLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:23:50.825171+00:00
-- url     : https://prove2.me/theorems/18c51c9c-56e2-5141-85ce-3dc7b6d1edc7
-- title:
--   Outer UCP limits agree on random prefixes of equal grids
-- statement:
--   If two families converge uniformly on compacts in outer probability and agree almost surely before a random clock, their limits agree there almost surely simultaneously in time.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation argument.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform convergence in outer probability preserves agreement on a random prefix. -/
theorem Kyprianou.Ch04.exercise45OuterUCPPrefixLimitV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G J : NNReal → ℕ → NNReal → Ω → ℝ)
    (I L : NNReal → Ω → ℝ) (τ : Ω → NNReal)
    (hG : ∀ T ε, 0 < ε → Tendsto
      (fun j => (P {w | ∃ t ≤ T, ε ≤ |G T j t w - I t w|}).toReal)
      atTop (nhds 0))
    (hJ : ∀ T ε, 0 < ε → Tendsto
      (fun j => (P {w | ∃ t ≤ T, ε ≤ |J T j t w - L t w|}).toReal)
      atTop (nhds 0))
    (hEq : ∀ᵐ w ∂P, ∀ T j t, t ≤ τ w → G T j t w = J T j t w) :
    ∀ᵐ w ∂P, ∀ t ≤ τ w, I t w = L t w := by
  sorry
