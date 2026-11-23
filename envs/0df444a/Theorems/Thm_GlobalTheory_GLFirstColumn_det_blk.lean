-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_det_blk
-- name    : GlobalTheory.GLFirstColumn.det_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:59.553664+00:00
-- url     : https://prove2.me/theorems/fbfc9b98-8cef-4f14-b210-a223903b7c25
-- title:
--   GLFirst Column: det blk
-- statement:
--   The GLFirst Column construction uses the det blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L296-L301

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

theorem GlobalTheory.GLFirstColumn.det_blk {k : ℕ} (r : Fin k → ℂ) (m : Fin k → Fin k → ℂ) :
    (Matrix.of (blk r m)).det = (Matrix.of m).det := by sorry
