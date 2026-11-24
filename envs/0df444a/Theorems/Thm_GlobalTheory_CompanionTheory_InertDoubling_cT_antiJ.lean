-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_cT_antiJ
-- name    : GlobalTheory.CompanionTheory.InertDoubling.cT_antiJ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:52.72844+00:00
-- url     : https://prove2.me/theorems/7cf51439-bc19-4e2c-87ee-72df6774b563
-- title:
--   Inert Doubling: c T anti J
-- statement:
--   The Inert Doubling construction uses the c T anti J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L100-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L100-L107

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

theorem GlobalTheory.CompanionTheory.InertDoubling.cT_antiJ {L : Type} [Field L] (σ : L →+* L) (n : ℕ) : cT σ (antiJ L n) = antiJ L n := by sorry
