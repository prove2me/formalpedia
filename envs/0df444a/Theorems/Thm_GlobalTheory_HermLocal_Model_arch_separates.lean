-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_Model_arch_separates
-- name    : GlobalTheory.HermLocal.Model.arch_separates
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:18.531216+00:00
-- url     : https://prove2.me/theorems/b420d3cf-7d66-53d9-a4a1-0757b4ab4562
-- title:
--   Model: arch separates
-- statement:
--   The Model construction uses the arch separates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SumSquaresNeThreeThreeAdic.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/SumSquaresNeThreeThreeAdic.lean#L139-L145

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

theorem GlobalTheory.HermLocal.Model.arch_separates (τ : E →+* ℂ) : ¬ ∃ Q : Matrix (Fin 1) (Fin 1) ℂ, Q.det ≠ 0 ∧
    (!![-1] : Matrix (Fin 1) (Fin 1) E).map τ =
      Qᵀ * (!![1] : Matrix (Fin 1) (Fin 1) E).map τ * Q.map conj := by sorry
