-- Prove2me | Theorems.Thm_GlobalTheory_T_functionFieldPlaceOrder_calculus
-- name    : GlobalTheory.T.functionFieldPlaceOrder_calculus
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:49.687028+00:00
-- url     : https://prove2.me/theorems/b5a70d73-9a32-4982-9db9-30ba234bd061
-- title:
--   T: function Field Place Order calculus
-- statement:
--   The T construction uses the function Field Place Order calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculusStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculusStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
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

theorem GlobalTheory.T.functionFieldPlaceOrder_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by sorry
