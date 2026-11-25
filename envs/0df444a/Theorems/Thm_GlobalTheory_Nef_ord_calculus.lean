-- Prove2me | Theorems.Thm_GlobalTheory_Nef_ord_calculus
-- name    : GlobalTheory.Nef.ord_calculus
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:05.998448+00:00
-- url     : https://prove2.me/theorems/33db617b-088b-4be7-aa8e-7a8506dbf32e
-- title:
--   Nef: ord calculus
-- statement:
--   The Nef construction uses the ord calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L135-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L135-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
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
set_option autoImplicit false
open GlobalTheory.Nef.OrdCalc

theorem GlobalTheory.Nef.ord_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by sorry
