-- Prove2me | Theorems.Thm_MultiPeriod_lowerSemicontinuous_lintegral_VGo
-- name    : MultiPeriod.lowerSemicontinuous_lintegral_VGo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:26.102382+00:00
-- url     : https://prove2.me/theorems/d6f23c0b-20c7-5ce1-93df-2eab363e2ac4
-- title:
--   Multi Period: lower Semicontinuous lintegral VGo
-- statement:
--   **The integrated Bellman value is lower semicontinuous in the initial
--       coupling.**  In the Feller/lsc model `VGo c κμ κν T 0` is lower
--       semicontinuous on the initial history space (`lowerSemicontinuous_VGo`
--       at `t = 0`, where `PairHist X Y 0` is definitionally `X 0 × Y 0`), and
--       integration against a probability measure preserves lower
--       semicontinuity for the weak topology
--       (`lowerSemicontinuous_lintegral_probabilityMeasure`).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L597-L610
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L597-L610

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

theorem MultiPeriod.lowerSemicontinuous_lintegral_VGo (T : ℕ)
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    LowerSemicontinuous (fun γ : WeakP (X 0 × Y 0) =>
      ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀
        ∂γ.toMeasure) := by sorry
