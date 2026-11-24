-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_st_one
-- name    : GlobalTheory.CompanionTheory.InertCorner.st_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:53:30.230648+00:00
-- url     : https://prove2.me/theorems/765ece13-f6a7-41b2-9ce5-d554558687a6
-- title:
--   Inert Corner: st one
-- statement:
--   The Inert Corner construction uses the st one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L27-L31

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

theorem GlobalTheory.CompanionTheory.InertCorner.st_one (σ : L →+* L) : st σ (1 : Matrix (Fin N) (Fin N) L) = 1 := by sorry
