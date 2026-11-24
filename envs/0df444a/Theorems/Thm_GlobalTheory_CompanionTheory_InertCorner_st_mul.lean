-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_st_mul
-- name    : GlobalTheory.CompanionTheory.InertCorner.st_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:01:27.4026+00:00
-- url     : https://prove2.me/theorems/a9e58572-8b75-4fed-9914-79bee7d99b7a
-- title:
--   Inert Corner: st mul
-- statement:
--   The Inert Corner construction uses the st mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L18-L21

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

theorem GlobalTheory.CompanionTheory.InertCorner.st_mul (σ : L →+* L) (A B : Matrix (Fin N) (Fin N) L) : st σ (A * B) = st σ B * st σ A := by sorry
