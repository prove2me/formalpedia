-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_stoppedBeta_distinguished_log_saving_all
-- name    : OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:20:58.549847+00:00
-- url     : https://prove2.me/theorems/3427cd04-ccdf-449e-929b-4d225010d51b
-- title:
--   OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedAllTuples.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedAllTuples.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_stoppedBeta_distinguished_log_saving_all (m : ℕ)
--       (hEF : AngularKummerPrimeExplicitEstimate)
--       (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F C ξ : ℝ}
--       (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
--       (hξ : 0 < ξ) (hgap : C < ξ*m) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (B ρ a b z u V : ℝ) (j : ℕ),
--         1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
--         Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
--         0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
--         |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
--         ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
--         (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
--         (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
--         (∀ d ∈ D₀, primary d) →
--         ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
--         norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
--         ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
--         ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
--           stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
--             (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
--               (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
--             (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
--           (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
--             then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/(Real.log X)^D
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.normTwist` and `OAI.CubicFirstMoment.primeCutoff` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.geometricBinCount`, `OAI.CubicFirstMoment.geometricBinLower` and `OAI.CubicFirstMoment.primeDetectorCutoff` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.orderedConvolutionSupport` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.angularCubicSymbol` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.distinguishedTupleCoefficient`, `OAI.CubicFirstMoment.primaryPairSupport` and `OAI.CubicFirstMoment.stoppedBeta` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.stoppedDistinguishedTest` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_angular_stoppedBeta_long_bins_log_saving` and `OAI.CubicFirstMoment.angular_stopped_noncube_mass` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedAllTuples.lean (declaration OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_distinguished_log_saving_all (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u V : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
      |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  sorry

end CubicFirstMoment

end

end OAI
end
