-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_conjT_sub
-- name    : GlobalTheory.FrameCompletion.conjT_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:01.762708+00:00
-- url     : https://prove2.me/theorems/65817f59-d148-41ec-abe8-5f59119b6267
-- title:
--   Frame Completion: conj T sub
-- statement:
--   The Frame Completion construction uses the conj T sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] {σ : L →+* L}

theorem GlobalTheory.FrameCompletion.conjT_sub {m p : Type} (A B : Matrix m p L) : cT σ (A - B) = cT σ A - cT σ B := by sorry
