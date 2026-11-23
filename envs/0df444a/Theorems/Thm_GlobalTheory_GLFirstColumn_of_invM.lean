-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_of_invM
-- name    : GlobalTheory.GLFirstColumn.of_invM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:14.710123+00:00
-- url     : https://prove2.me/theorems/ad08495d-7aa9-4419-ba2f-dc408fca8933
-- title:
--   GLFirst Column: of inv M
-- statement:
--   The GLFirst Column construction uses the of inv M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L71-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L71-L71

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

theorem GlobalTheory.GLFirstColumn.of_invM {m : ℕ} (x : Fin m → Fin m → ℂ) : Matrix.of (invM x) = (Matrix.of x)⁻¹ := by sorry
