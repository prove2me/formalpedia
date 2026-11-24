-- Prove2me | Theorems.Thm_GlobalTheory_Chamber_vecSpan_mono
-- name    : GlobalTheory.Chamber.vecSpan_mono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:32.510911+00:00
-- url     : https://prove2.me/theorems/67b0fa1f-0b13-45a9-9d6f-601b5518db1e
-- title:
--   Chamber: vec Span mono
-- statement:
--   The Chamber construction uses the vec Span mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L104-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L104-L104

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

theorem GlobalTheory.Chamber.vecSpan_mono {P Q : Finset (SV k)} (e : Q ⊆ P) : aP Q ≤ aP P := by sorry
