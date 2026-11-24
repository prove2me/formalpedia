-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_isInt_antiJ
-- name    : GlobalTheory.CompanionTheory.InertDoubling.isInt_antiJ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:01:53.026636+00:00
-- url     : https://prove2.me/theorems/d06be3a8-b58d-43bb-aae6-acde9f7a6bcf
-- title:
--   Inert Doubling: is Int anti J
-- statement:
--   The Inert Doubling construction uses the is Int anti J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L92-L96

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertDoubling.isInt_antiJ (n : ℕ) : IsInt (antiJ L n) := by sorry
