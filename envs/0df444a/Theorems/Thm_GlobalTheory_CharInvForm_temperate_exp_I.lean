-- Prove2me | Theorems.Thm_GlobalTheory_CharInvForm_temperate_exp_I
-- name    : GlobalTheory.CharInvForm.temperate_exp_I
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:59.652801+00:00
-- url     : https://prove2.me/theorems/77b40403-cd05-4694-ae92-118dfae891e3
-- title:
--   Char Inv Form: temperate exp I
-- statement:
--   The Char Inv Form construction uses the temperate exp I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationInvariantFunctionalLinearZero.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationInvariantFunctionalLinearZero.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CharInvForm

theorem GlobalTheory.CharInvForm.temperate_exp_I : Function.HasTemperateGrowth (fun y : ℝ => Complex.exp (Complex.I * y)) := by sorry
