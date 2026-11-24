-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_wt_cancel
-- name    : GlobalTheory.GLFirstColumn.wt_cancel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:27.63426+00:00
-- url     : https://prove2.me/theorems/0d7affa0-2f53-4d66-bd27-161b905abb68
-- title:
--   GLFirst Column: wt cancel
-- statement:
--   The GLFirst Column construction uses the wt cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L105-L110

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

theorem GlobalTheory.GLFirstColumn.wt_cancel {m : ℕ} (a : Fin m → Fin m → ℂ) (ha : (Matrix.of a).det ≠ 0) :
    ENNReal.ofReal ((‖(Matrix.of a).det‖ ^ 2) ^ m) * wt a = 1 := by sorry
