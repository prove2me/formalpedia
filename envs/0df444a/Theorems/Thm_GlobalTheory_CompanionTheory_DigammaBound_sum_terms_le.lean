-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_sum_terms_le
-- name    : GlobalTheory.CompanionTheory.DigammaBound.sum_terms_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:57.393803+00:00
-- url     : https://prove2.me/theorems/87b96510-922e-4437-b0ad-4a8248ec7bad
-- title:
--   Digamma Bound: sum terms le
-- statement:
--   The Digamma Bound construction uses the sum terms le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L61-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L61-L82

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

theorem GlobalTheory.CompanionTheory.DigammaBound.sum_terms_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (hn : M ≤ n) :
    ∑ i ∈ range n, ‖1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))‖ ≤
      2 * ∑ i ∈ range M, ((i : ℝ) + 1)⁻¹ + ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) := by sorry
