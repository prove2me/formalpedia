-- Prove2me | Theorems.Thm_MultiPeriod_measurableSet_argminSet_hit
-- name    : MultiPeriod.measurableSet_argminSet_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:48.862965+00:00
-- url     : https://prove2.me/theorems/81450b64-1482-5210-b335-f6698c8af0ee
-- title:
--   Multi Period: measurable Set argmin Set hit
-- statement:
--   **M2: the argmin correspondence is weakly measurable.** Hit-sets of
--       open sets are Borel: decompose the open set into countably many
--       closed sets; on each, compare the constrained and unconstrained
--       values (both lower semicontinuous, hence Borel).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L370-L398
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L370-L398

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

theorem MultiPeriod.measurableSet_argminSet_hit
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {U : Set (WeakP (X (t + 1) × Y (t + 1)))} (hU : IsOpen U) :
    MeasurableSet {h | (argminSet κμP κνP t F h ∩ U).Nonempty} := by sorry
