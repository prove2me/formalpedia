-- Prove2me | Theorems.Thm_GlobalTheory_StandardAdditiveCharacter_bijective_dual_addChar
-- name    : GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:22:22.819888+00:00
-- url     : https://prove2.me/theorems/6faff40e-0d71-45f3-8050-f65f5edaf0da
-- title:
--   Standard Additive Character: bijective dual add Char
-- statement:
--   The Standard Additive Character construction uses the bijective dual add Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveDualAddChar.lean#L14-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveDualAddChar.lean#L14-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveDualAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StandardAdditiveCharacter

theorem GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun (φ : Module.Dual (ZMod n) A) ↦
      AddChar.compAddMonoidHom ZMod.stdAddChar (LinearMap.toAddMonoidHom φ) := by sorry
