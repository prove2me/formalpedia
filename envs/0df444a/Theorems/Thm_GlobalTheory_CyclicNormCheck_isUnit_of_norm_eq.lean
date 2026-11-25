-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_isUnit_of_norm_eq
-- name    : GlobalTheory.CyclicNormCheck.isUnit_of_norm_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:44.959439+00:00
-- url     : https://prove2.me/theorems/982eb502-918f-4f5e-88fe-4b57262d311f
-- title:
--   Cyclic Norm Check: is Unit of norm eq
-- statement:
--   The Cyclic Norm Check construction uses the is Unit of norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L20-L30

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

theorem GlobalTheory.CyclicNormCheck.isUnit_of_norm_eq {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] {x : F} (hx : x ≠ 0) {y : K ⊗[F] E}
    (h : Algebra.norm K y = algebraMap F K x) : IsUnit y := by sorry
