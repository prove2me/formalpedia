-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_rightcont_weight_factor
-- name    : Kyprianou.Ch04.cor412_rightcont_weight_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:13:48.295869+00:00
-- url     : https://prove2.me/theorems/a068a799-8c1e-5961-b072-6c560ecb3c63
-- title:
--   Right-continuous filtration finite stopped-history and future-path reward factorisation
-- statement:
--   Right-continuous filtration finite stopped-history and future-path reward factorisation.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The right-continuous filtration supports arbitrary measurable stopped-history weights. -/

theorem Kyprianou.Ch04.cor412_rightcont_weight_factor
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (τ : Ω → NNReal)
    (hτ : ∀ s : NNReal, MeasurableSet[F.rightCont s] {w : Ω | τ w ≤ s})
    (W : Ω → ℝ≥0∞) (hW : Measurable W)
    (hPast : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] W)
    (R : (NNReal → ℝ) → ℝ≥0∞) (hR : Measurable R) :
    (∫⁻ w, W w * R (fun t => L.X (τ w + t) w - L.X (τ w) w) ∂P) =
      (∫⁻ w, W w ∂P) * (∫⁻ w, R (fun t => L.X t w) ∂P) := by sorry
