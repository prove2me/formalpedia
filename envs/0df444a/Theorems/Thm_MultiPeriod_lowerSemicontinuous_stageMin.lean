-- Prove2me | Theorems.Thm_MultiPeriod_lowerSemicontinuous_stageMin
-- name    : MultiPeriod.lowerSemicontinuous_stageMin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:31.53091+00:00
-- url     : https://prove2.me/theorems/c0a2ab30-34cb-44f0-b2e3-8bae963e2693
-- title:
--   Multi Period: lower Semicontinuous stage Min
-- statement:
--   **Berge minimum (parametrized).** In the Feller model, the constrained
--       one-step value against a jointly lower semicontinuous objective and a
--       closed constraint set is lower semicontinuous in the history:
--       minimizers along a convergent sequence of histories have convergent
--       marginals, hence are tight; Prokhorov extracts a convergent
--       subsequence whose limit is feasible, constrained, and no worse.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L132-L204
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L132-L204

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

theorem MultiPeriod.lowerSemicontinuous_stageMin
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    LowerSemicontinuous (stageMin κμP κνP t F C) := by sorry
