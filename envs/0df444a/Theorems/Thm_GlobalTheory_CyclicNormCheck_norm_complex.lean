-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_complex
-- name    : GlobalTheory.CyclicNormCheck.norm_complex
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:39.584795+00:00
-- url     : https://prove2.me/theorems/378282c2-62c9-484b-b665-c112ba97fbaa
-- title:
--   Cyclic Norm Check: norm complex
-- statement:
--   The Cyclic Norm Check construction uses the norm complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L37-L40

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

theorem GlobalTheory.CyclicNormCheck.norm_complex {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℂ]
    [Module.Finite F E] (a : ℂ) : ∃ y : ℂ ⊗[F] E, Algebra.norm ℂ y = a := by sorry
