-- Prove2me | Theorems.Thm_GlobalTheory_T_continuous_matrix_coefficient
-- name    : GlobalTheory.T.continuous_matrix_coefficient
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:20.090372+00:00
-- url     : https://prove2.me/theorems/867db8c0-6dc9-40bf-b7e9-e07be54e94ab
-- title:
--   T: continuous matrix coefficient
-- statement:
--   The T construction uses the continuous matrix coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousMatrixCoefficientStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousMatrixCoefficientStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficient
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficientStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuous_matrix_coefficient : ∀ (n : ℕ) (g g' : Sch (Fin n)), Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by sorry
