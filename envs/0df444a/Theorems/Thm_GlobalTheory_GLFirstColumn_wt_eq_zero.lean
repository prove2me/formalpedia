-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_wt_eq_zero
-- name    : GlobalTheory.GLFirstColumn.wt_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:27.875584+00:00
-- url     : https://prove2.me/theorems/a217f14d-3f05-41f8-9c57-4903de4484fc
-- title:
--   GLFirst Column: wt eq zero
-- statement:
--   The GLFirst Column construction uses the wt eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L112-L115

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

theorem GlobalTheory.GLFirstColumn.wt_eq_zero {m : ℕ} (a : Fin m → Fin m → ℂ) (ha : (Matrix.of a).det = 0) : wt a = 0 := by sorry
