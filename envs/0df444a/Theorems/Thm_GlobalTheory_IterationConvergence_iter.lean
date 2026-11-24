-- Prove2me | Theorems.Thm_GlobalTheory_IterationConvergence_iter
-- name    : GlobalTheory.IterationConvergence.iter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:47.620803+00:00
-- url     : https://prove2.me/theorems/8cb90767-e876-4946-9084-ec10b47120e1
-- title:
--   Iteration Convergence: iter
-- statement:
--   The Iteration Convergence construction uses the iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsTer.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsTer.lean#L18-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IterationConvergence

theorem GlobalTheory.IterationConvergence.iter {z : ℂ} (hz : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by sorry
