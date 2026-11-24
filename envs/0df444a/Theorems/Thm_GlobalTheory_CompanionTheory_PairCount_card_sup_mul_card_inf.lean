-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PairCount_card_sup_mul_card_inf
-- name    : GlobalTheory.CompanionTheory.PairCount.card_sup_mul_card_inf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:43.143199+00:00
-- url     : https://prove2.me/theorems/29a16a3c-0e46-4c8b-90a8-ce996098b2f6
-- title:
--   Pair Count: card sup mul card inf
-- statement:
--   The Pair Count construction uses the card sup mul card inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorIntersectionCard.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorIntersectionCard.lean#L15-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorIntersectionCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PairCount

theorem GlobalTheory.CompanionTheory.PairCount.card_sup_mul_card_inf {R X : Type} [Ring R] [AddCommGroup X] [Module R X] [Finite X]
    (I L : Submodule R X) :
    Nat.card ↥(I ⊔ L) * Nat.card ↥(I ⊓ L) = Nat.card ↥I * Nat.card ↥L := by sorry
