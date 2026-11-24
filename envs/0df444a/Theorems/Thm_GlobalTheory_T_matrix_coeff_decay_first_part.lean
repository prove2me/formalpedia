-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_coeff_decay_first_part
-- name    : GlobalTheory.T.matrix_coeff_decay_first_part
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:41.30262+00:00
-- url     : https://prove2.me/theorems/8d6d61e1-5a1b-4dcd-9782-fc98765162b6
-- title:
--   T: matrix coeff decay first part
-- statement:
--   The T construction uses the matrix coeff decay first part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecayFirstPartStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecayFirstPartStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPartStatement
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

theorem GlobalTheory.T.matrix_coeff_decay_first_part : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by sorry
