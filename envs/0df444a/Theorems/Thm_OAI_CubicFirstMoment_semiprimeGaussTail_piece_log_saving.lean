-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_semiprimeGaussTail_piece_log_saving
-- name    : OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:45:30.677186+00:00
-- url     : https://prove2.me/theorems/09947118-e539-4eab-b078-1681088debec
-- title:
--   OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving` of [lean/OAI/NumberTheory/CubicMoment/Estimates/SemiprimeGaussTailBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SemiprimeGaussTailBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem semiprimeGaussTail_piece_log_saving
--       (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
--       ∃ (K : ℝ) (m : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (H U : ℝ) (i j : ℕ), 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
--         (1+Real.log X)^m ≤ U → U < 2*Real.pi*H →
--         ‖semiprimeGaussTailPiece 0 H U X i j‖ ≤
--           K*X^(5/6:ℝ)/(1+Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.GammaQuotientStripBound` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.semiprimeGaussTailPiece` (definitions bundle `OAIQ096A019` of this split).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SemiprimeGaussTailBound.lean (declaration OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving)

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
open scoped BigOperators
namespace CubicFirstMoment

theorem semiprimeGaussTail_piece_log_saving
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (K : ℝ) (m : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H U : ℝ) (i j : ℕ), 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      (1+Real.log X)^m ≤ U → U < 2*Real.pi*H →
      ‖semiprimeGaussTailPiece 0 H U X i j‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
