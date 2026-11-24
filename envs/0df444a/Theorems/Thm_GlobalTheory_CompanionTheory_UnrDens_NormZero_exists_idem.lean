-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_exists_idem
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormZero.exists_idem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:07.829377+00:00
-- url     : https://prove2.me/theorems/b6511176-ae99-4b2a-9399-e9d7cde3b43c
-- title:
--   Norm Zero: exists idem
-- statement:
--   The Norm Zero construction uses the exists idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L52-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L52-L87

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

theorem GlobalTheory.CompanionTheory.UnrDens.NormZero.exists_idem (h : ResAlg E τ q ε) (hf : ¬ IsField E) :
    ∃ e : E, e * e = e ∧ τ e = 1 - e := by sorry
