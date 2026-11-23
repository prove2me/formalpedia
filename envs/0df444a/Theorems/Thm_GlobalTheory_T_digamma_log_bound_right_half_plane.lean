-- Prove2me | Theorems.Thm_GlobalTheory_T_digamma_log_bound_right_half_plane
-- name    : GlobalTheory.T.digamma_log_bound_right_half_plane
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:38.028394+00:00
-- url     : https://prove2.me/theorems/faa5df0f-0d1d-4113-a8c4-2675b65d165f
-- title:
--   T: digamma log bound right half plane
-- statement:
--   The T construction uses the digamma log bound right half plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlaneStatement.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlaneStatement.lean#L4-L5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.digamma_log_bound_right_half_plane : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by sorry
