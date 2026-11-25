-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_Model_hyperbolic_hyp
-- name    : GlobalTheory.HermLocal.Model.hyperbolic_hyp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:53.303182+00:00
-- url     : https://prove2.me/theorems/41b4f1c5-78ab-56e6-937f-83e3de7615ee
-- title:
--   Model: hyperbolic hyp
-- statement:
--   The Model construction uses the hyperbolic hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SumSquaresNeThreeThreeAdic.lean#L125-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SumSquaresNeThreeThreeAdic.lean#L125-L137

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HermLocal.Model.hyperbolic_hyp :
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      CongrOver (v.adicCompletion (maximalRealSubfield E))
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) !![2, 0; 0, -2]) ∧
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
      (!![2, 0; 0, -2] : Matrix (Fin 2) (Fin 2) E).map τ =
        Qᵀ * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E).map τ * Q.map conj) := by sorry
