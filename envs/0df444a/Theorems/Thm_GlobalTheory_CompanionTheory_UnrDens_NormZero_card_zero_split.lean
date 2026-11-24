-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_card_zero_split
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormZero.card_zero_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:05.727198+00:00
-- url     : https://prove2.me/theorems/9bf74c4b-dcee-49a6-b5b2-8ab64ad8df49
-- title:
--   Norm Zero: card zero split
-- statement:
--   The Norm Zero construction uses the card zero split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L111-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L111-L156

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

theorem GlobalTheory.CompanionTheory.UnrDens.NormZero.card_zero_split (h : ResAlg E τ q ε) {e : E} (he : e * e = e) (hτ : τ e = 1 - e) :
    Nat.card {a : E // a * τ a = 0} + 1 = 2 * q := by sorry
