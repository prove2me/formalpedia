-- Prove2me | Theorems.Thm_GlobalTheory_T_glCharacter_factors_through_det_of_two_ne_zero
-- name    : GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:49.981267+00:00
-- url     : https://prove2.me/theorems/d2adfb70-e01c-4f50-b2ed-5dd676631936
-- title:
--   T: gl Character factors through det of two ne zero
-- statement:
--   The T construction uses the gl Character factors through det of two ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZeroStatement.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZeroStatement.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by sorry
