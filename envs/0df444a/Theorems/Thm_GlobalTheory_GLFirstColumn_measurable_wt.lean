-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_wt
-- name    : GlobalTheory.GLFirstColumn.measurable_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:27.575591+00:00
-- url     : https://prove2.me/theorems/84bb6a94-ad59-4339-b291-da471cb14402
-- title:
--   GLFirst Column: measurable wt
-- statement:
--   The GLFirst Column construction uses the measurable wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L98-L99

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

theorem GlobalTheory.GLFirstColumn.measurable_wt {m : ℕ} : Measurable (wt : (Fin m → Fin m → ℂ) → ℝ≥0∞) := by sorry
