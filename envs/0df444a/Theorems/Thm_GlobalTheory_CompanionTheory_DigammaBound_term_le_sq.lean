-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_term_le_sq
-- name    : GlobalTheory.CompanionTheory.DigammaBound.term_le_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:59.894207+00:00
-- url     : https://prove2.me/theorems/4ce65d41-4069-4479-a839-92fadae8f80b
-- title:
--   Digamma Bound: term le sq
-- statement:
--   The Digamma Bound construction uses the term le sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L53-L59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaBound
open Finset

theorem GlobalTheory.CompanionTheory.DigammaBound.term_le_sq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ ‖z‖ / ((k : ℝ) + 1) ^ 2 := by sorry
