-- Prove2me | Theorems.Thm_GlobalTheory_T_functionFieldOneVariable_transcendental_finite_and_ext
-- name    : GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:47.913641+00:00
-- url     : https://prove2.me/theorems/5f5c3556-5706-4b33-9111-625388222e0c
-- title:
--   T: function Field One Variable transcendental finite and ext
-- statement:
--   The T construction uses the function Field One Variable transcendental finite and ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldOneVariableTranscendentalFiniteAndEStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldOneVariableTranscendentalFiniteAndEStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndE
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndEStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F → (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧ ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by sorry
