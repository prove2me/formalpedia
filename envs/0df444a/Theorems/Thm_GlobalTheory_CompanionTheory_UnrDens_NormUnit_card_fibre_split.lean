-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fibre_split
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre_split
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:19:59.107719+00:00
-- url     : https://prove2.me/theorems/0a258a0f-ce35-436b-8a94-a0d70408dbba
-- title:
--   Norm Unit: card fibre split
-- statement:
--   The Norm Unit construction uses the card fibre split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L104-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L104-L148

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

theorem GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre_split (h : ResAlg E τ q ε) (hnf : ¬ IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q - 1 := by sorry
