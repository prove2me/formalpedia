-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleL2MaximalV1
-- name    : Kyprianou.Ch04.rightContinuousMartingaleL2MaximalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:29:46.24298+00:00
-- url     : https://prove2.me/theorems/b535ab8d-a91e-482e-be97-a39dd0515305
-- title:
--   Doob L2 maximal estimate for right-continuous real martingales
-- statement:
--   A real martingale with almost surely right-continuous paths and an integrable terminal square has integrable squared horizon supremum with expectation at most four times its terminal second moment.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii), Doob maximal inequality.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem rightContinuousMartingaleL2MaximalV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P) (T : ℝ≥0) (hT : 0 < T)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun s => M s ω)
      (nhdsWithin t (Ioi t)) (nhds (M t ω)))
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    Integrable (fun ω => sSup ((fun t : ℝ≥0 => |M t ω|^2) '' Iic T)) P ∧
      (∫ ω, sSup ((fun t : ℝ≥0 => |M t ω|^2) '' Iic T) ∂P) ≤
        4 * ∫ ω, (M T ω)^2 ∂P := by
  sorry
end Kyprianou.Ch04
