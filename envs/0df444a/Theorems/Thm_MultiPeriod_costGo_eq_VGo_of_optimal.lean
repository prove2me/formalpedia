-- Prove2me | Theorems.Thm_MultiPeriod_costGo_eq_VGo_of_optimal
-- name    : MultiPeriod.costGo_eq_VGo_of_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:29.043312+00:00
-- url     : https://prove2.me/theorems/65081f95-96a0-4fe9-9fad-7db8dd2b9772
-- title:
--   Multi Period: cost Go eq VGo of optimal
-- statement:
--   A stage-wise exactly optimal feasible strategy attains the Bellman
--       value: `costGo = VGo` at time-consistent depths (the ε = 0 instance
--       of L2 + L4; no new induction). Stated for arbitrary Markov kernels —
--       Feller is not needed once the strategy exists.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L470-L486
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L470-L486

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

theorem MultiPeriod.costGo_eq_VGo_of_optimal
    {κμ : (t : ℕ) → XHist X t → Measure (X (t + 1))}
    {κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1))} (T : ℕ)
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (γ : Strat X Y) (hmem : ∀ t h, γ t h ∈ Feas κμ κν t h)
    (hopt : ∀ t (h : PairHist X Y t),
      ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γ t h)
        ≤ ⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) :
    ∀ (k t : ℕ), t + k = T → ∀ h : PairHist X Y t,
      costGo c γ k t h = VGo c κμ κν k t h := by sorry
