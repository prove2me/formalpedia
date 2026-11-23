-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_wt_mul
-- name    : GlobalTheory.GLFirstColumn.wt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:35.370683+00:00
-- url     : https://prove2.me/theorems/8fe666b0-b727-4a95-87bc-4b8218de8dc2
-- title:
--   GLFirst Column: wt mul
-- statement:
--   The GLFirst Column construction uses the wt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L101-L103

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

theorem GlobalTheory.GLFirstColumn.wt_mul {m : ℕ} (a y : Fin m → Fin m → ℂ) : wt (mulM a y) = wt a * wt y := by sorry
