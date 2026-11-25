-- Prove2me | Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_nonneg
-- name    : GlobalTheory.FlowScaling.maxFlow_nonneg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:32.909831+00:00
-- url     : https://prove2.me/theorems/82e65b80-5b68-4860-b3cc-f16a0eebb655
-- title:
--   Flow Scaling: max Flow nonneg
-- statement:
--   The Flow Scaling construction uses the max Flow nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L52-L55

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

theorem GlobalTheory.FlowScaling.maxFlow_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    0 ≤ maxFlow l d D := by sorry
