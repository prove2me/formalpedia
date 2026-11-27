-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ZeroTimeObstruction
-- name    : Kyprianou.Ch04.exercise45ZeroTimeObstruction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:55:13.774555+00:00
-- url     : https://prove2.me/theorems/d32bdee4-115f-4a4f-8d33-e89c3ce60a95
-- title:
--   Unbounded arbitrary initial left weight prevents physical grid UCP
-- statement:
--   On a trivial sigma algebra an arbitrary unbounded initial weight defeats outer probability convergence of the physical clipped drift grids to the quadratic Ito value.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), formal boundary audit.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The exact physical UCP predicate fails for an unbounded arbitrary zero-time weight. -/
theorem Kyprianou.Ch04.exercise45ZeroTimeObstruction {Ω : Type} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m = ⊥)
    (a : Ω → ℝ) (ha : ∀ n : ℕ, ∃ w, a w = (n : ℝ))
    (I : NNReal → Ω → ℝ)
    (hI : ∀ᵐ w ∂P, ∀ t : NNReal, I t w = (t : ℝ)^2) :
    ¬ Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P
      (fun t _ => (t : ℝ))
      (fun s w => 2 * (if s = 0 then a w else (s : ℝ))) I := by
  sorry
