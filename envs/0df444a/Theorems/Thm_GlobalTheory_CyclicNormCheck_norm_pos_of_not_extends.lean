-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_pos_of_not_extends
-- name    : GlobalTheory.CyclicNormCheck.norm_pos_of_not_extends
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:15.032097+00:00
-- url     : https://prove2.me/theorems/182cca77-d0a1-4d8d-83c4-0cc8fc76eea5
-- title:
--   Cyclic Norm Check: norm pos of not extends
-- statement:
--   The Cyclic Norm Check construction uses the norm pos of not extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L46-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L46-L85

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck

theorem GlobalTheory.CyclicNormCheck.norm_pos_of_not_extends {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
    [Module.Finite F E] (σ : F →+* ℝ) (hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ)
    {y : E} (hy : y ≠ 0) : 0 < σ (Algebra.norm F y) := by sorry
