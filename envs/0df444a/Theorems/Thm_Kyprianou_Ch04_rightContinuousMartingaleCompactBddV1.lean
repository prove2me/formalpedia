-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleCompactBddV1
-- name    : Kyprianou.Ch04.rightContinuousMartingaleCompactBddV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:21.07295+00:00
-- url     : https://prove2.me/theorems/8dbbebd5-727c-4764-aefb-98b0ed342713
-- title:
--   Compact square boundedness of right-continuous martingales
-- statement:
--   Compact square boundedness of right-continuous martingales.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem rightContinuousMartingaleCompactBddV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P) (T : ℝ≥0) (hT : 0 < T)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun s => M s ω)
      (nhdsWithin t (Ioi t)) (nhds (M t ω)))
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    ∀ᵐ ω ∂P, BddAbove ((fun t : ℝ≥0 => |M t ω|^2) '' Iic T) := by
  sorry
end Kyprianou.Ch04
