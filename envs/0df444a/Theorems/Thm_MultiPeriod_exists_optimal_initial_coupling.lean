-- Prove2me | Theorems.Thm_MultiPeriod_exists_optimal_initial_coupling
-- name    : MultiPeriod.exists_optimal_initial_coupling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:42.757911+00:00
-- url     : https://prove2.me/theorems/1139cbb3-9f0a-4e78-9510-cff506b7954b
-- title:
--   Multi Period: exists optimal initial coupling
-- statement:
--   **Attainment of the OUTER infimum (Phase 5, initial-coupling half).**
--       In the Feller/lsc model there is an initial coupling `γ₀*` of `μ₀` and
--       `ν₀` minimising the integrated Bellman value: a lower semicontinuous
--       function on a nonempty compact set attains its infimum
--       (`LowerSemicontinuousOn.exists_isMinOn`), applied here to the weakly
--       compact set of couplings.  This is the `γ₀`-side companion of
--       `bellman_value_attained_measurable`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L619-L651
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L619-L651

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

theorem MultiPeriod.exists_optimal_initial_coupling (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ γ₀ : Measure (X 0 × Y 0), γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      IsProbabilityMeasure γ₀ ∧
      ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ ∂γ₀
        = ⨅ (γ₀' : Measure (X 0 × Y 0)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
            ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ ∂γ₀' := by sorry
