-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PairCount_card_comap_subtype
-- name    : GlobalTheory.CompanionTheory.PairCount.card_comap_subtype
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:00.861651+00:00
-- url     : https://prove2.me/theorems/a8a13a63-cb87-46be-bdab-45c5902bdd2f
-- title:
--   Pair Count: card comap subtype
-- statement:
--   The Pair Count construction uses the card comap subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorIntersectionCard.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorIntersectionCard.lean#L6-L13

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

theorem GlobalTheory.CompanionTheory.PairCount.card_comap_subtype {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (p q : Submodule R X) :
    Nat.card ↥(q.comap p.subtype) = Nat.card ↥(p ⊓ q) := by sorry
