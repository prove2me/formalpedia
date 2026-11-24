-- Prove2me | Theorems.Thm_GlobalTheory_ZModDual_card_dual_eq
-- name    : GlobalTheory.ZModDual.card_dual_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:16.312944+00:00
-- url     : https://prove2.me/theorems/22cc2f45-33a4-4cea-8367-26e9a67b6ef8
-- title:
--   ZMod Dual: card dual eq
-- statement:
--   The ZMod Dual construction uses the card dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardDualZmodModuleEqCard.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardDualZmodModuleEqCard.lean#L18-L23

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

theorem GlobalTheory.ZModDual.card_dual_eq (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A]
    [Finite A] : Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by sorry
