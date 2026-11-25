-- Prove2me | Theorems.Thm_GlobalTheory_FlowScaling_mul_maxFlow_le
-- name    : GlobalTheory.FlowScaling.mul_maxFlow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:30.29592+00:00
-- url     : https://prove2.me/theorems/4c21ee68-de38-4dd9-95cf-02cec17d360b
-- title:
--   Flow Scaling: mul max Flow le
-- statement:
--   The Flow Scaling construction uses the mul max Flow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L57-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L57-L74

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowScaling
variable {l d : ℕ} [NeZero d]

theorem GlobalTheory.FlowScaling.mul_maxFlow_le (hl : 1 ≤ l) {c : ℝ} {D D' : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a)
    (h : ∀ a, c * D a ≤ D' a) : c * maxFlow l d D ≤ maxFlow l d D' := by sorry
