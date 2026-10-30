-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_bounded_large_common_nonzero
-- name    : OAI.CubicFirstMoment.bounded_large_common_nonzero
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:58:27.392821+00:00
-- url     : https://prove2.me/theorems/323eb98e-3ccc-4235-b063-072fac8f89c1
-- title:
--   OAI.CubicFirstMoment.bounded_large_common_nonzero: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.bounded_large_common_nonzero` of [lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedCommonPowers.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedCommonPowers.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem bounded_large_common_nonzero (V : ℝ → ℂ)
--       (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
--       ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
--         (Z A M u : ℝ), 2 ≤ Z → 0 < A → (Z/2)^(3/4:ℝ) ≤ A →
--         (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
--         (∀ a ∈ S, ‖β a‖ ≤ M) →
--         ‖∑ k ∈ (commonRowFactors S).filter (fun k => (Z/2)^(1/4:ℝ) ≤ norm k),
--           (commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k-
--             commonGramZeroMode S (fun a => star (dispersionAmplitude β u a)) V A k)‖ ≤
--           K*A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)*M^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.commonRowFactors` and `OAI.CubicFirstMoment.dispersionAmplitude` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.commonGramBlock` and `OAI.CubicFirstMoment.commonGramZeroMode` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.bounded_rough_divisor_common_log_saving` and `OAI_CubicFirstMoment_bounded_rough_divisor_variance_remainder` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedCommonPowers.lean (declaration OAI.CubicFirstMoment.bounded_large_common_nonzero)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A008

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_large_common_nonzero (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A M u : ℝ), 2 ≤ Z → 0 < A → (Z/2)^(3/4:ℝ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => (Z/2)^(1/4:ℝ) ≤ norm k),
        (commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k-
          commonGramZeroMode S (fun a => star (dispersionAmplitude β u a)) V A k)‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)*M^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
