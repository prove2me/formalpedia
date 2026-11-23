-- Prove2me | Theorems.Thm_GlobalTheory_IterationConvergence_step
-- name    : GlobalTheory.IterationConvergence.step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:20.776384+00:00
-- url     : https://prove2.me/theorems/d2292b1a-ef98-42d5-b112-11137076b01c
-- title:
--   Iteration Convergence: step
-- statement:
--   The Iteration Convergence construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsTer.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsTer.lean#L5-L16

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

theorem GlobalTheory.IterationConvergence.step (w : ℂ) (h : ‖w - 1‖ < 1 / 2) : (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by sorry
