-- Prove2me | Theorems.Thm_MultiPeriod_bellman_value_eq_multi_measurable
-- name    : MultiPeriod.bellman_value_eq_multi_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:33.116963+00:00
-- url     : https://prove2.me/theorems/1167ba05-27b7-5288-b3b1-f1052b685885
-- title:
--   Multi Period: bellman value eq multi measurable
-- statement:
--   **Corollary (Phase 4).** The multi-period Bellman value
--       representation holds with the strategy infimum restricted to
--       strategies that are σ(Σ¹₁)-measurable at every stage — measurability
--       costs nothing in the value. Upper bound via the measurable ε-optimal
--       strategy and L4; lower bound inherited from `bellman_value_eq_multi`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L129-L193
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L129-L193

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

theorem MultiPeriod.bellman_value_eq_multi_measurable (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h)
      (_ : ∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        AnalyticallyMeasurable φ ∧ ∀ h, γ t h = (φ h).toMeasure),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := by sorry
