-- Prove2me | Theorems.Thm_GlobalTheory_FlowScaling_mul_flowVal_le
-- name    : GlobalTheory.FlowScaling.mul_flowVal_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:30.017925+00:00
-- url     : https://prove2.me/theorems/4517d02e-5089-4150-87fb-c65841605355
-- title:
--   Flow Scaling: mul flow Val le
-- statement:
--   The Flow Scaling construction uses the mul flow Val le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean#L12-L28

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

theorem GlobalTheory.FlowScaling.mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    (l : ℝ) * flowVal d x ≤ ∑ a, D a := by sorry
