-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fibre_field
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre_field
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:20:20.131188+00:00
-- url     : https://prove2.me/theorems/7ca506b3-4801-4aba-8719-5c00242e8b10
-- title:
--   Norm Unit: card fibre field
-- statement:
--   The Norm Unit construction uses the card fibre field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L233-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L233-L295

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

theorem GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre_field (h : ResAlg E τ q ε) (hf : IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q + 1 := by sorry
