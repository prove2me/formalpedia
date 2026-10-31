-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_semiprime_block_log_saving_actual
-- name    : OAI.CubicFirstMoment.semiprime_block_log_saving_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:45:27.381123+00:00
-- url     : https://prove2.me/theorems/0c599667-e82a-4fbe-b854-0de521ae8d24
-- title:
--   OAI.CubicFirstMoment.semiprime_block_log_saving_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.semiprime_block_log_saving_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralSemiprimeBlockEstimate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralSemiprimeBlockEstimate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem semiprime_block_log_saving_actual
--       (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       (k U : ℕ) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T : ℝ) (i j : ℕ) (u : ℝ),
--         semiprimePartitionPiece 0 H T X i j ≠ 0 → |u| ≤ (1+Real.log X)^U →
--         ‖semiprimeBlockPolynomial X i j u‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.GammaQuotientStripBound` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.KummerPrimeSiegelWalfisz` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.semiprimeBlockPolynomial` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.semiprimePartitionPiece` (definitions bundle `OAIQ096A019` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.primeProductLowHeight_sub_low_scale_isLittleO_actual` and `OAI_CubicFirstMoment_semiprime_piece_log_saving_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralSemiprimeBlockEstimate.lean (declaration OAI.CubicFirstMoment.semiprime_block_log_saving_actual)

import Mathlib
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem semiprime_block_log_saving_actual
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (k U : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T : ℝ) (i j : ℕ) (u : ℝ),
      semiprimePartitionPiece 0 H T X i j ≠ 0 → |u| ≤ (1+Real.log X)^U →
      ‖semiprimeBlockPolynomial X i j u‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
