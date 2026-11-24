-- Prove2me | Theorems.Thm_GlobalTheory_IterativeScalingBound_step
-- name    : GlobalTheory.IterativeScalingBound.step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:36.275731+00:00
-- url     : https://prove2.me/theorems/f7151e35-303a-4d63-a08b-1363a23231b6
-- title:
--   Iterative Scaling Bound: step
-- statement:
--   The Iterative Scaling Bound construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerAlt.lean#L5-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerAlt.lean#L5-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IterativeScalingBound

theorem GlobalTheory.IterativeScalingBound.step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by sorry
