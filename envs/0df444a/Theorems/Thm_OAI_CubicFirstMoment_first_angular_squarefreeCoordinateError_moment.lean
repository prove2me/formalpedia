-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_first_angular_squarefreeCoordinateError_moment
-- name    : OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:25:06.610775+00:00
-- url     : https://prove2.me/theorems/31c24a34-ff6c-4da0-a619-8d7a2ae117d3
-- title:
--   OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularSquarefreeCoordinateErrors.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularSquarefreeCoordinateErrors.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--    theorem first_angular_squarefreeCoordinateError_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (q : ι → Eisenstein)
--         (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
--         (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
--         (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
--         (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
--         (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
--         (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/32)) →
--         (∑ a ∈ P, ‖angularSquarefreeCoordinateError ℓ a 1 q η t W X V Y‖^2) ≤
--           C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*(2*Y)^(7/3-c/4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.angularSquarefreeCoordinateError` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_exceptional_residual_moment` and `OAI_CubicFirstMoment_angular_full_exceptional_structured_moment` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularSquarefreeCoordinateErrors.lean (declaration OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_angular_squarefreeCoordinateError_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/32)) →
      (∑ a ∈ P, ‖angularSquarefreeCoordinateError ℓ a 1 q η t W X V Y‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*(2*Y)^(7/3-c/4) := by
  sorry

end CubicFirstMoment

end

end OAI
end
