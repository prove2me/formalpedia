-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZModDual_nat_card_dual_eq
-- name    : GlobalTheory.CompanionTheory.ZModDual.nat_card_dual_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:17.298805+00:00
-- url     : https://prove2.me/theorems/d60ae7f2-4c65-4711-bd43-58cc4a2aad19
-- title:
--   ZMod Dual: nat card dual eq
-- statement:
--   The ZMod Dual construction uses the nat card dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NatCardDualEq.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NatCardDualEq.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NatCardDualEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZModDual

theorem GlobalTheory.CompanionTheory.ZModDual.nat_card_dual_eq : ∀ (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N] [Finite N],
    Nat.card (Module.Dual (ZMod n) N) = Nat.card N := by sorry
