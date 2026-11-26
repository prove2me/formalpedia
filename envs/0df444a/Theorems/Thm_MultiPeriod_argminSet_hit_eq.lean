-- Prove2me | Theorems.Thm_MultiPeriod_argminSet_hit_eq
-- name    : MultiPeriod.argminSet_hit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:23.044581+00:00
-- url     : https://prove2.me/theorems/3df8f6cc-6204-590d-9247-9564224138c4
-- title:
--   Multi Period: argmin Set hit eq
-- statement:
--   **M1: the argmin hit-set identity.** Hitting a closed constraint set
--       with an exact minimizer is equivalent to the constrained fiber being
--       nonempty and the constrained value not exceeding the unconstrained
--       one (attainment on the compact constrained fiber).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L292-L320
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L292-L320

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

theorem MultiPeriod.argminSet_hit_eq (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    {h | (argminSet κμP κνP t F h ∩ C).Nonempty}
      = {h | ({γ | (h, γ) ∈ FeasGraph
            (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty}
        ∩ {h | stageMin κμP κνP t F C h ≤ stageMin κμP κνP t F univ h} := by sorry
