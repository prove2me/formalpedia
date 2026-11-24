-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_partial_le
-- name    : GlobalTheory.CompanionTheory.DigammaBound.partial_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:43.977529+00:00
-- url     : https://prove2.me/theorems/cad905da-fffb-4540-a1ae-b502bd2ebafb
-- title:
--   Digamma Bound: partial le
-- statement:
--   The Digamma Bound construction uses the partial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L87-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L87-L144

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

theorem GlobalTheory.CompanionTheory.DigammaBound.partial_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (hzM : ‖z‖ ≤ M)
    (n : ℕ) (hn : M ≤ n) :
    ‖((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ))‖ ≤
      6 + 2 * Real.log M := by sorry
