-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_large_common_nonzero_power
-- name    : OAI.CubicFirstMoment.large_common_nonzero_power
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:01:01.281976+00:00
-- url     : https://prove2.me/theorems/775ecea6-bb4f-402f-8763-e61de879a5b1
-- title:
--   OAI.CubicFirstMoment.large_common_nonzero_power: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.large_common_nonzero_power` of [lean/OAI/NumberTheory/CubicMoment/Estimates/LargeCommonSaving.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/LargeCommonSaving.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem large_common_nonzero_power {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
--       (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
--       ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (v : Eisenstein → ℂ)
--         (A N : ℝ), 0 < A → 1 ≤ N → N^(1-δ) ≤ A →
--         (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
--         ‖∑ k ∈ (commonRowFactors S).filter (fun k => N^δ ≤ norm k),
--           (commonGramBlock S v V A k-commonGramZeroMode S v V A k)‖ ≤
--         K*A^(2/3:ℝ)*N^(2/3-δ/8)*∑ a ∈ S, ‖v a‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.commonRowFactors` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.commonGramBlock` and `OAI.CubicFirstMoment.commonGramZeroMode` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_tailPrime_middle_group`, `OAI.CubicFirstMoment.bounded_large_common_nonzero`, `OAI_CubicFirstMoment_primeGroupTail_wide_bilinear_log_saving`, `OAI.CubicFirstMoment.semiprimeGaussTailAngular_isLittleO`, `OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving` and `OAI.CubicFirstMoment.tailPrime_middle_group` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/LargeCommonSaving.lean (declaration OAI.CubicFirstMoment.large_common_nonzero_power)

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
namespace CubicFirstMoment

theorem large_common_nonzero_power {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (A N : ℝ), 0 < A → 1 ≤ N → N^(1-δ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => N^δ ≤ norm k),
        (commonGramBlock S v V A k-commonGramZeroMode S v V A k)‖ ≤
      K*A^(2/3:ℝ)*N^(2/3-δ/8)*∑ a ∈ S, ‖v a‖^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
