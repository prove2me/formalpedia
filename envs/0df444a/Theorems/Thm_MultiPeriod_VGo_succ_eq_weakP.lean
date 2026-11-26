-- Prove2me | Theorems.Thm_MultiPeriod_VGo_succ_eq_weakP
-- name    : MultiPeriod.VGo_succ_eq_weakP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:35.233619+00:00
-- url     : https://prove2.me/theorems/460ace8d-2de8-4061-b387-df437afd2418
-- title:
--   Multi Period: VGo succ eq weak P
-- statement:
--   The one-step infimum of `VGo` reindexed over the Polish space of
--       probability measures: legitimate because feasible one-step plans are
--       probability measures (Markov kernels).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L166-L175
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L166-L175

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
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
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]

theorem MultiPeriod.VGo_succ_eq_weakP
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x)) (k t : ℕ)
    (h : PairHist X Y t) :
    VGo c κμ κν (k + 1) t h
      = c t h + ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
          (_ : (h, γ) ∈ FeasGraph κμ κν t),
          ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γ.toMeasure := by sorry
