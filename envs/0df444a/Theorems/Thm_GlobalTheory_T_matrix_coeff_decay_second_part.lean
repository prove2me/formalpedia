-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_coeff_decay_second_part
-- name    : GlobalTheory.T.matrix_coeff_decay_second_part
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:41.134329+00:00
-- url     : https://prove2.me/theorems/c495fc4a-4180-474d-bf05-453923944231
-- title:
--   T: matrix coeff decay second part
-- statement:
--   The T construction uses the matrix coeff decay second part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPartStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPartStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPartStatement
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

theorem GlobalTheory.T.matrix_coeff_decay_second_part : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖qPart w‖) ^ N ≤ C := by sorry
