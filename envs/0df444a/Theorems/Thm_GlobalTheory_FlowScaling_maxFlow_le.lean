-- Prove2me | Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_le
-- name    : GlobalTheory.FlowScaling.maxFlow_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:23:30.097628+00:00
-- url     : https://prove2.me/theorems/23f3ec4f-185a-4bfb-9b24-205947e34bae
-- title:
--   Flow Scaling: max Flow le
-- statement:
--   The Flow Scaling construction uses the max Flow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L42-L46

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

theorem GlobalTheory.FlowScaling.maxFlow_le {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) {B : ℝ}
    (h : ∀ x, IsFlow l d D x → flowVal d x ≤ B) : maxFlow l d D ≤ B := by sorry
