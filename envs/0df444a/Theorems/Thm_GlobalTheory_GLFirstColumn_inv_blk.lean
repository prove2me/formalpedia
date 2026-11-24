-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_inv_blk
-- name    : GlobalTheory.GLFirstColumn.inv_blk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:24.832793+00:00
-- url     : https://prove2.me/theorems/c04ce59e-2a86-447a-9c03-62759a145d97
-- title:
--   GLFirst Column: inv blk
-- statement:
--   The GLFirst Column construction uses the inv blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L303-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L303-L314

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

theorem GlobalTheory.GLFirstColumn.inv_blk {k : ℕ} (T : Fin k → ℂ) (m : Fin k → Fin k → ℂ) (hm : (Matrix.of m).det ≠ 0) :
    (Matrix.of (blk (-T) m))⁻¹ = Matrix.of (blk (T ᵥ* Matrix.of (invM m)) (invM m)) := by sorry
