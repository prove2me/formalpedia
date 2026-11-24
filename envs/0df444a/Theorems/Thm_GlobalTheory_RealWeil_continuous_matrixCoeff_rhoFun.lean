-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_continuous_matrixCoeff_rhoFun
-- name    : GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:38.708346+00:00
-- url     : https://prove2.me/theorems/9afa0869-7354-47a2-b073-d81d9d6e472d
-- title:
--   Real Weil: continuous matrix Coeff rho Fun
-- statement:
--   The Real Weil construction uses the continuous matrix Coeff rho Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousMatrixCoefficient.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousMatrixCoefficient.lean#L8-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficient
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
open GlobalTheory GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by sorry
