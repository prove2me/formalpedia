-- Prove2me | Theorems.Thm_GlobalTheory_ZModDual_card_quot_ker_le
-- name    : GlobalTheory.ZModDual.card_quot_ker_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:12.211091+00:00
-- url     : https://prove2.me/theorems/70122ee7-c0b3-43f5-b76d-6d7f2725e20e
-- title:
--   ZMod Dual: card quot ker le
-- statement:
--   The ZMod Dual construction uses the card quot ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardKerMulCardEq.lean#L6-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardKerMulCardEq.lean#L6-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKerMulCardEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZModDual

theorem GlobalTheory.ZModDual.card_quot_ker_le (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A] [Module (ZMod n) A]
    [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (A ⧸ LinearMap.ker b) ≤ Nat.card (B ⧸ LinearMap.ker b.flip) := by sorry
