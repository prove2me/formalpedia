-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_mulM
-- name    : GlobalTheory.GLFirstColumn.measurable_mulM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:12.393673+00:00
-- url     : https://prove2.me/theorems/9eb78d3c-001f-4580-8f17-f5486e4bd2e5
-- title:
--   GLFirst Column: measurable mul M
-- statement:
--   The GLFirst Column construction uses the measurable mul M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L73-L79

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

theorem GlobalTheory.GLFirstColumn.measurable_mulM {m : ℕ} {α : Type*} [MeasurableSpace α] {u v : α → Fin m → Fin m → ℂ}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun a => mulM (u a) (v a) := by sorry
