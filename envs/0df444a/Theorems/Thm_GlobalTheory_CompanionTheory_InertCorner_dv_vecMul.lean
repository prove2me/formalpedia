-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_dv_vecMul
-- name    : GlobalTheory.CompanionTheory.InertCorner.dv_vecMul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:02:28.788202+00:00
-- url     : https://prove2.me/theorems/8948bb61-94c2-44e5-a8e3-057f17a6907b
-- title:
--   Inert Corner: dv vec Mul
-- statement:
--   The Inert Corner construction uses the dv vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L33-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertCorner.dv_vecMul (σ : L →+* L) (x : Fin N → L) (A : Matrix (Fin N) (Fin N) L) :
    dv σ (x ᵥ* A) = st σ A *ᵥ dv σ x := by sorry
