-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_coeff_continuous_rapid_decay
-- name    : GlobalTheory.T.matrix_coeff_continuous_rapid_decay
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:29.962927+00:00
-- url     : https://prove2.me/theorems/25c994b8-9a27-4bd4-b0d7-56b5cfbb648e
-- title:
--   T: matrix coeff continuous rapid decay
-- statement:
--   The T construction uses the matrix coeff continuous rapid decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecayStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecayStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecay
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecayStatement
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

theorem GlobalTheory.T.matrix_coeff_continuous_rapid_decay : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by sorry
