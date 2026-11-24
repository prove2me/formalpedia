-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_isInt_st
-- name    : GlobalTheory.CompanionTheory.InertCorner.isInt_st
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:02:14.54989+00:00
-- url     : https://prove2.me/theorems/5f9957a9-c6af-4f63-a42a-c8ae8214719a
-- title:
--   Inert Corner: is Int st
-- statement:
--   The Inert Corner construction uses the is Int st property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L70-L77

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
variable [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertCorner.isInt_st {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {A : Matrix (Fin N) (Fin N) L} (hA : IsInt A) :
    IsInt (st σ A) := by sorry
