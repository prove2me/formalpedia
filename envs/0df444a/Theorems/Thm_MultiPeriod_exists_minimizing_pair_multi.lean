-- Prove2me | Theorems.Thm_MultiPeriod_exists_minimizing_pair_multi
-- name    : MultiPeriod.exists_minimizing_pair_multi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:04.886536+00:00
-- url     : https://prove2.me/theorems/58dcdd8b-e1a3-4d82-b1fb-7da4e6dd0381
-- title:
--   Multi Period: exists minimizing pair multi
-- statement:
--   **Phase 5, full attainment — competitor form.**  Unfolding the infimum
--       of `bellman_value_attained_multi`: the exhibited pair `(γ₀*, γopt)` is
--       feasible, its strategy half is plain-Borel measurable, and no feasible
--       competitor `(γ₀', γ)` does better.  This is the statement "the
--       `T`-period bicausal optimal transport problem has an optimal solution"
--       in the Feller/lsc model.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L715-L738
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L715-L738

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

theorem MultiPeriod.exists_minimizing_pair_multi (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ (γ₀ : Measure (X 0 × Y 0)) (γopt : Strat X Y),
      γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) ∧
      ∀ (γ₀' : Measure (X 0 × Y 0)) (γ : Strat X Y),
        γ₀' ∈ CouplingSet₀ μ₀ ν₀ →
        (∀ t h, γ t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) →
        ∫⁻ h₀, costGo c γopt T 0 h₀ ∂γ₀
          ≤ ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀' := by sorry
