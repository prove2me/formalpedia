-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_Model_unramified_two_classes
-- name    : GlobalTheory.HermLocal.Model.unramified_two_classes
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:58.540856+00:00
-- url     : https://prove2.me/theorems/309be2cb-3094-4f66-9c6f-c355353c7f56
-- title:
--   Model: unramified two classes
-- statement:
--   The Model construction uses the unramified two classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SumSquaresNeThreeThreeAdic.lean#L100-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SumSquaresNeThreeThreeAdic.lean#L100-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HermLocal
open GlobalTheory GlobalTheory.HermLocal GlobalTheory.HermLocal.Model

theorem GlobalTheory.HermLocal.Model.unramified_two_classes : ¬ ∃ P : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℚ_[3] (-1) 0),
    P.det ≠ 0 ∧ !![1, 0; 0, 1] = Pᵀ * !![1, 0; 0, 3] * P.map (conjSqrt (-1)) := by sorry
