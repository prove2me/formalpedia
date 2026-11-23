-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_invM
-- name    : GlobalTheory.GLFirstColumn.measurable_invM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:13.846579+00:00
-- url     : https://prove2.me/theorems/5a0ed071-e815-4d59-b4f8-b0823b7e6cbc
-- title:
--   GLFirst Column: measurable inv M
-- statement:
--   The GLFirst Column construction uses the measurable inv M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L84-L93

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

theorem GlobalTheory.GLFirstColumn.measurable_invM {m : ℕ} :
    Measurable (invM : (Fin m → Fin m → ℂ) → Fin m → Fin m → ℂ) := by sorry
