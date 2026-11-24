-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_mem
-- name    : GlobalTheory.CompanionTheory.InertCorner.H_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:00:32.440802+00:00
-- url     : https://prove2.me/theorems/90c82b2d-25f4-4e84-9bc0-83127674f2ae
-- title:
--   Inert Corner: H mem
-- statement:
--   The Inert Corner construction uses the H mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L79-L88

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

theorem GlobalTheory.CompanionTheory.InertCorner.H_mem {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {A : Matrix (Fin N) (Fin N) L} (hA : IsInt A)
    {x : Fin N → L} (hx : ∀ j, x j ∈ intL L) : H σ x A x ∈ intL L := by sorry
