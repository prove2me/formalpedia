-- Prove2me | Theorems.Thm_MultiPeriod_stageF_lowerSemianalytic
-- name    : MultiPeriod.stageF_lowerSemianalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:59.073935+00:00
-- url     : https://prove2.me/theorems/e1bff33e-9da0-4a04-a30d-d9d006166be1
-- title:
--   Multi Period: stage F lower Semianalytic
-- statement:
--   The integrated tail value is lower semianalytic on the product of the
--       history space with the space of probability measures: BS 7.48 applied
--       to the evaluation kernel `(h, γ) ↦ γ`
--       (`lintegral_weakP_lowerSemianalytic`), with the integrand lower
--       semianalytic by Phase 3.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L62-L73
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L62-L73

import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Definitions.Def_BicausalOT_MeasurableStrategy
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

theorem MultiPeriod.stageF_lowerSemianalytic
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t)) (k t : ℕ) :
    IsLowerSemianalytic
      (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
        ∫⁻ z, VGo c κμ κν k (t + 1) (p.1, z) ∂p.2.toMeasure) := by sorry
