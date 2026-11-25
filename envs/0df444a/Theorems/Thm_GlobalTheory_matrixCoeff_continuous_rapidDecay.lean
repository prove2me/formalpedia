-- Prove2me | Theorems.Thm_GlobalTheory_matrixCoeff_continuous_rapidDecay
-- name    : GlobalTheory.matrixCoeff_continuous_rapidDecay
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:09:47.341002+00:00
-- url     : https://prove2.me/theorems/a8e84454-3809-492c-991f-866bcd04f00a
-- title:
--   Global Theory: matrix Coeff continuous rapid Decay
-- statement:
--   The Global Theory construction uses the matrix Coeff continuous rapid Decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecay.lean#L37-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecay.lean#L37-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecay
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
open GlobalTheory
open MatrixCoeff

theorem GlobalTheory.matrixCoeff_continuous_rapidDecay : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by sorry
