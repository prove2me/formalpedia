-- Prove2me | Theorems.Thm_GlobalTheory_T_functionFieldPlace_sum_order_eq_finrank
-- name    : GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:06.070968+00:00
-- url     : https://prove2.me/theorems/fd2b096e-37a7-4201-9267-c3557986d2aa
-- title:
--   T: function Field Place sum order eq finrank
-- statement:
--   The T construction uses the function Field Place sum order eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrankStatement.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrankStatement.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrankStatement
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

theorem GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by sorry
