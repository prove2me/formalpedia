-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_digamma_bound
-- name    : GlobalTheory.CompanionTheory.DigammaBound.digamma_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:11.124251+00:00
-- url     : https://prove2.me/theorems/0e9ed193-6e12-4e4c-84c1-e221e6d270aa
-- title:
--   Digamma Bound: digamma bound
-- statement:
--   The Digamma Bound construction uses the digamma bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L146-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L146-L170

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

theorem GlobalTheory.CompanionTheory.DigammaBound.digamma_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by sorry
