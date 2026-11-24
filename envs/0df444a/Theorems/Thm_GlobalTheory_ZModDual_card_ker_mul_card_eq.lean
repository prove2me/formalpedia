-- Prove2me | Theorems.Thm_GlobalTheory_ZModDual_card_ker_mul_card_eq
-- name    : GlobalTheory.ZModDual.card_ker_mul_card_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:51.229747+00:00
-- url     : https://prove2.me/theorems/734570fc-8dac-4953-8c43-30273fb12c98
-- title:
--   ZMod Dual: card ker mul card eq
-- statement:
--   The ZMod Dual construction uses the card ker mul card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardKerMulCardEq.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardKerMulCardEq.lean#L28-L39

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

theorem GlobalTheory.ZModDual.card_ker_mul_card_eq (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A]
    [Module (ZMod n) A] [Finite A] [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (LinearMap.ker b) * Nat.card B = Nat.card (LinearMap.ker b.flip) * Nat.card A := by sorry
