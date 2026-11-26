-- Prove2me | Theorems.Thm_MultiPeriod_bellman_value_attained_multi
-- name    : MultiPeriod.bellman_value_attained_multi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:46.236543+00:00
-- url     : https://prove2.me/theorems/61673b2b-9db6-4415-adb8-8a50907f972f
-- title:
--   Multi Period: bellman value attained multi
-- statement:
--   **Phase 5, full attainment.**  In the Feller/lsc model the two-level
--       infimum of `bellman_value_eq_multi` — over initial couplings AND over
--       pointwise feasible strategies — is a MINIMUM: it is attained at an
--       explicit pair `(γ₀*, γopt)` consisting of a weakly optimal initial
--       coupling (`exists_optimal_initial_coupling`) and a stagewise exactly
--       optimal, plain-Borel measurable strategy
--       (`bellman_value_attained_measurable`).  The two halves are independent:
--       the strategy attains the value pointwise in `h₀`, hence after
--       integration against *any* initial coupling, and the coupling then
--       minimises what is left.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L665-L707
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L665-L707

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

theorem MultiPeriod.bellman_value_attained_multi (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ (γ₀ : Measure (X 0 × Y 0)) (γopt : Strat X Y),
      γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      IsProbabilityMeasure γ₀ ∧
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) ∧
      ∫⁻ h₀, costGo c γopt T 0 h₀ ∂γ₀
        = ⨅ (γ₀' : Measure (X 0 × Y 0)) (γ : Strat X Y)
            (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
            (_ : ∀ t h, γ t h ∈ Feas
              (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) t h),
            ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀' := by sorry
