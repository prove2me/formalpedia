-- Prove2me | Theorems.Thm_GlobalTheory_ZModDual_stdAddChar_comp_bijective
-- name    : GlobalTheory.ZModDual.stdAddChar_comp_bijective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:28.105504+00:00
-- url     : https://prove2.me/theorems/0534af2c-38e0-4f5b-8dea-fd99a6dbfa5f
-- title:
--   ZMod Dual: std Add Char comp bijective
-- statement:
--   The ZMod Dual construction uses the std Add Char comp bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardDualZmodModuleEqCard.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardDualZmodModuleEqCard.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveDualAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZModDual

theorem GlobalTheory.ZModDual.stdAddChar_comp_bijective (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun φ : Module.Dual (ZMod n) A =>
      ((ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom : AddChar A ℂ) := by sorry
