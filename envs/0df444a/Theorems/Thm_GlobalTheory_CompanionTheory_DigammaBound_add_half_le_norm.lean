-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_add_half_le_norm
-- name    : GlobalTheory.CompanionTheory.DigammaBound.add_half_le_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:59.197362+00:00
-- url     : https://prove2.me/theorems/9ef56d02-18fd-4030-8fb6-3aefd90f7716
-- title:
--   Digamma Bound: add half le norm
-- statement:
--   The Digamma Bound construction uses the add half le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L8-L14

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

theorem GlobalTheory.CompanionTheory.DigammaBound.add_half_le_norm (z : ℂ) (hz : 1 / 2 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    x + 1 / 2 ≤ ‖z + (x : ℂ)‖ := by sorry
