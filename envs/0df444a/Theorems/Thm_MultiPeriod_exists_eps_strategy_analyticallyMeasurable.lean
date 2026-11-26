-- Prove2me | Theorems.Thm_MultiPeriod_exists_eps_strategy_analyticallyMeasurable
-- name    : MultiPeriod.exists_eps_strategy_analyticallyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:44.798566+00:00
-- url     : https://prove2.me/theorems/c89b1c11-26f9-5af5-896e-40bfa159372d
-- title:
--   Multi Period: exists eps strategy analytically Measurable
-- statement:
--   **Phase 4 (BS Proposition 7.50 analogue).** For Borel Markov kernels
--       and lower semianalytic stage costs, the ε-optimal strategy of
--       `exists_eps_strategy` can be chosen σ(Σ¹₁)-measurable at every stage:
--       each `γε t` factors through an `AnalyticallyMeasurable` map into the
--       Polish space of probability measures.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L82-L120
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L82-L120

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

theorem MultiPeriod.exists_eps_strategy_analyticallyMeasurable (T : ℕ)
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γε : Strat X Y,
      (∀ t h, γε t h ∈ Feas κμ κν t h) ∧
      (∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
          ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        AnalyticallyMeasurable φ ∧ ∀ h, γε t h = (φ h).toMeasure) := by sorry
