-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_of_mulM
-- name    : GlobalTheory.GLFirstColumn.of_mulM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:21.192808+00:00
-- url     : https://prove2.me/theorems/979cff4f-1658-4e5e-8238-32bbb1dbf75b
-- title:
--   GLFirst Column: of mul M
-- statement:
--   The GLFirst Column construction uses the of mul M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L68-L69

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

theorem GlobalTheory.GLFirstColumn.of_mulM {m : ℕ} (x y : Fin m → Fin m → ℂ) :
    Matrix.of (mulM x y) = Matrix.of x * Matrix.of y := by sorry
