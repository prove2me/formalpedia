-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_quot_lev_succ
-- name    : GlobalTheory.CompanionTheory.UnrDens.card_quot_lev_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:26.688133+00:00
-- url     : https://prove2.me/theorems/2fff98c6-cdd6-474c-b5f9-98a8b5158dd6
-- title:
--   Unr Dens: card quot lev succ
-- statement:
--   The Unr Dens construction uses the card quot lev succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuotientCard.lean#L33-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuotientCard.lean#L33-L67

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens

theorem GlobalTheory.CompanionTheory.UnrDens.card_quot_lev_succ {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    Nat.card (R ⧸ lev ϖ (k + 1)) = Nat.card (R ⧸ lev ϖ 1) * Nat.card (R ⧸ lev ϖ k) := by sorry
