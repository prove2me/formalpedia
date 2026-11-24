-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_st_add
-- name    : GlobalTheory.CompanionTheory.InertCorner.st_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:01:24.944166+00:00
-- url     : https://prove2.me/theorems/76ca562e-2e95-4645-8df1-e9cd953db623
-- title:
--   Inert Corner: st add
-- statement:
--   The Inert Corner construction uses the st add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L23-L25

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

theorem GlobalTheory.CompanionTheory.InertCorner.st_add (σ : L →+* L) (A B : Matrix (Fin N) (Fin N) L) : st σ (A + B) = st σ A + st σ B := by sorry
