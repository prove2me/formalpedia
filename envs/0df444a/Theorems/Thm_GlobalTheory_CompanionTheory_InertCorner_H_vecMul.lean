-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_vecMul
-- name    : GlobalTheory.CompanionTheory.InertCorner.H_vecMul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:00:34.512901+00:00
-- url     : https://prove2.me/theorems/e0942998-0296-4e84-96cf-f5b1ea8c9705
-- title:
--   Inert Corner: H vec Mul
-- statement:
--   The Inert Corner construction uses the H vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L39-L42

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

theorem GlobalTheory.CompanionTheory.InertCorner.H_vecMul (σ : L →+* L) (x y : Fin N → L) (A P Q : Matrix (Fin N) (Fin N) L) :
    H σ (x ᵥ* P) A (y ᵥ* Q) = H σ x (P * A * st σ Q) y := by sorry
