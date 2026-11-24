-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_cT_submatrix
-- name    : GlobalTheory.CompanionTheory.InertDoubling.cT_submatrix
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:02:13.305794+00:00
-- url     : https://prove2.me/theorems/70576a8d-f02d-4492-8548-4d5fb9a01c37
-- title:
--   Inert Doubling: c T submatrix
-- statement:
--   The Inert Doubling construction uses the c T submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L60-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] {σ : L →+* L} {m p : Type}

theorem GlobalTheory.CompanionTheory.InertDoubling.cT_submatrix {ι : Type} (e : m ≃ ι) (M : Matrix m m L) :
    cT σ (M.submatrix e.symm e.symm) = (cT σ M).submatrix e.symm e.symm := by sorry
