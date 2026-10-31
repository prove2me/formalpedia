-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_bounded_rough_divisor_common_log_saving
-- name    : OAI.CubicFirstMoment.bounded_rough_divisor_common_log_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:23:41.640429+00:00
-- url     : https://prove2.me/theorems/1857e75b-ed60-418f-bebf-a673247c7c4a
-- title:
--   OAI.CubicFirstMoment.bounded_rough_divisor_common_log_saving: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.bounded_rough_divisor_common_log_saving` of [lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedCommonLogSaving.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedCommonLogSaving.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem bounded_rough_divisor_common_log_saving (hpnt : PrimaryPrimePNT)
--       (hHuxley : HuxleyAdditiveLargeSieve) {κ : ℝ} (hκ : 0 < κ)
--       (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
--       ∃ (K : ℝ) (j : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ) (b A M u R : ℝ)
--           (d : Eisenstein), X^κ ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A →
--         A ≤ b^2/(Real.log X)^(3*k) → 0 ≤ M →
--         (Real.log X)^(6*(j+k)) ≤ R → primary d →
--         norm d ≤ b^(1/1000:ℝ) → (norm d)^4 ≤ R →
--         (∀ a ∈ S, primary a ∧ Squarefree a ∧ b/2 ≤ norm a ∧ norm a ≤ b) →
--         (∀ a ∈ S, ‖β a‖ ≤ M) →
--         (∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p) →
--         ‖divisorDispersionVariance d S β u V A-divisorCoprimeDispersionGram d S β u V A‖ ≤
--           K*A^(2/3:ℝ)*b^(5/3:ℝ)*M^2/(Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.divisorDispersionVariance` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.divisorCoprimeDispersionGram` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm`, `OAI.CubicFirstMoment.primary` and `OAI.CubicFirstMoment.primaryPrime` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_stopped_sieved_model_log_saving` and `OAI.CubicFirstMoment.stopped_sieved_model_log_saving` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedCommonLogSaving.lean (declaration OAI.CubicFirstMoment.bounded_rough_divisor_common_log_saving)

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
namespace CubicFirstMoment

theorem bounded_rough_divisor_common_log_saving (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve) {κ : ℝ} (hκ : 0 < κ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (K : ℝ) (j : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ) (b A M u R : ℝ)
        (d : Eisenstein), X^κ ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A →
      A ≤ b^2/(Real.log X)^(3*k) → 0 ≤ M →
      (Real.log X)^(6*(j+k)) ≤ R → primary d →
      norm d ≤ b^(1/1000:ℝ) → (norm d)^4 ≤ R →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ b/2 ≤ norm a ∧ norm a ≤ b) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      (∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p) →
      ‖divisorDispersionVariance d S β u V A-divisorCoprimeDispersionGram d S β u V A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)*M^2/(Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
