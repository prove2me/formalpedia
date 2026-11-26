-- Prove2me | Theorems.Thm_MultiPeriod_exists_optimal_measurable_strategy
-- name    : MultiPeriod.exists_optimal_measurable_strategy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:21.839328+00:00
-- url     : https://prove2.me/theorems/ee589ed6-5932-4172-8956-bb317ae455fc
-- title:
--   Multi Period: exists optimal measurable strategy
-- statement:
--   **Phase 5 main theorem (BS 8.3 analogue).** In the Feller/lsc model
--       there is a strategy that is pointwise feasible, EXACTLY optimal at
--       every stage (time-consistent depth, ε = 0), and plain-Borel
--       measurable: each stage factors through a `Measurable` map into the
--       Polish space of probability measures — strictly stronger
--       measurability than Phase 4's σ(Σ¹₁), under strictly stronger
--       hypotheses.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L409-L459
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L409-L459

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

theorem MultiPeriod.exists_optimal_measurable_strategy (T : ℕ)
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ γopt : Strat X Y,
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1) (t + 1)
            (h, z) ∂(γopt t h)
          ≤ ⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
                (fun t y => (κνP t y : Measure (Y (t + 1)))) t h),
              ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
                (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1)
                (t + 1) (h, z) ∂γm) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) := by sorry
