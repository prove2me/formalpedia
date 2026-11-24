-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_blk
-- name    : GlobalTheory.GLFirstColumn.measurable_blk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:35.903818+00:00
-- url     : https://prove2.me/theorems/90fd5581-9541-44bb-976a-193ab098b981
-- title:
--   GLFirst Column: measurable blk
-- statement:
--   The GLFirst Column construction uses the measurable blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L316-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L316-L324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn

theorem GlobalTheory.GLFirstColumn.measurable_blk {k : ℕ} {α : Type*} [MeasurableSpace α] {u : α → Fin k → ℂ}
    {v : α → Fin k → Fin k → ℂ} (hu : Measurable u) (hv : Measurable v) :
    Measurable fun t => blk (u t) (v t) := by sorry
