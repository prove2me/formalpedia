-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_continuous_detM
-- name    : GlobalTheory.GLFirstColumn.continuous_detM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:15.683612+00:00
-- url     : https://prove2.me/theorems/66a8312d-b466-4803-b4bc-ef383d79957b
-- title:
--   GLFirst Column: continuous det M
-- statement:
--   The GLFirst Column construction uses the continuous det M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L81-L82

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

theorem GlobalTheory.GLFirstColumn.continuous_detM {m : ℕ} : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det := by sorry
