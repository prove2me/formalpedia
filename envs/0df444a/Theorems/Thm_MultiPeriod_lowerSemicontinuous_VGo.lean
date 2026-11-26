-- Prove2me | Theorems.Thm_MultiPeriod_lowerSemicontinuous_VGo
-- name    : MultiPeriod.lowerSemicontinuous_VGo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:16.075802+00:00
-- url     : https://prove2.me/theorems/e83afbe3-61e6-5e31-91cd-674233802e64
-- title:
--   Multi Period: lower Semicontinuous VGo
-- statement:
--   **Phase 5, V1 (BS 8.3 analogue).** For Feller kernels and lower
--       semicontinuous stage costs, every Bellman value function is lower
--       semicontinuous on the history space (backward induction; the
--       integrand is jointly lsc by the integral pairing, the infimum by the
--       Berge minimum).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L213-L246
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L213-L246

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

theorem MultiPeriod.lowerSemicontinuous_VGo
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∀ k t : ℕ, LowerSemicontinuous
      (VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) k t) := by sorry
