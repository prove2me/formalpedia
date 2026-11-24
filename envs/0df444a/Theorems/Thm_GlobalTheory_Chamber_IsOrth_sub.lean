-- Prove2me | Theorems.Thm_GlobalTheory_Chamber_IsOrth_sub
-- name    : GlobalTheory.Chamber.IsOrth.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:50.122473+00:00
-- url     : https://prove2.me/theorems/2e524ff9-eca8-40d3-b918-04c8536bda6c
-- title:
--   Is Orth: sub
-- statement:
--   The Is Orth construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L191-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L191-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}

theorem GlobalTheory.Chamber.IsOrth.sub {𝔞 : Submodule ℝ (A0 k)} {X Y : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) (h' : IsOrth 𝔞 Y) :
    IsOrth 𝔞 (X - Y) := by sorry
