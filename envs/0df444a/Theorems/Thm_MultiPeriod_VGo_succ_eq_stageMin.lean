-- Prove2me | Theorems.Thm_MultiPeriod_VGo_succ_eq_stageMin
-- name    : MultiPeriod.VGo_succ_eq_stageMin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:41.295264+00:00
-- url     : https://prove2.me/theorems/bd072690-bd9e-4bc2-a2a0-31a8c078b638
-- title:
--   Multi Period: VGo succ eq stage Min
-- statement:
--   The one-step Bellman recursion through the unconstrained
--       `stageMin`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L113-L122
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L113-L122

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
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]

theorem MultiPeriod.VGo_succ_eq_stageMin (k t : ℕ) (h : PairHist X Y t) :
    VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) (k + 1) t h
      = c t h + stageMin κμP κνP t
          (fun p => ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1) (p.1, z)
            ∂p.2.toMeasure) univ h := by sorry
