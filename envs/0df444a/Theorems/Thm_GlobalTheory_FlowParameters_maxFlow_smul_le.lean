-- Prove2me | Theorems.Thm_GlobalTheory_FlowParameters_maxFlow_smul_le
-- name    : GlobalTheory.FlowParameters.maxFlow_smul_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:44.048816+00:00
-- url     : https://prove2.me/theorems/5629946a-ded2-4671-9797-50e029a36c16
-- title:
--   Flow Parameters: max Flow smul le
-- statement:
--   The Flow Parameters construction uses the max Flow smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ParametersSmallBound.lean#L29-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ParametersSmallBound.lean#L29-L52

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowParameters

theorem GlobalTheory.FlowParameters.maxFlow_smul_le (l d : ℕ) [NeZero d] (c : ℝ) (hc : 0 ≤ c) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    maxFlow l d (fun a => c * D a) ≤ c * maxFlow l d D := by sorry
