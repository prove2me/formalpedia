-- Prove2me | Theorems.Thm_GlobalTheory_T_isQuadraticSqrtExtension_basic_facts
-- name    : GlobalTheory.T.isQuadraticSqrtExtension_basic_facts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:58.779153+00:00
-- url     : https://prove2.me/theorems/604831d6-1b81-494d-bffa-def130e0d96b
-- title:
--   T: is Quadratic Sqrt Extension basic facts
-- statement:
--   The T construction uses the is Quadratic Sqrt Extension basic facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFactsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFactsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFactsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isQuadraticSqrtExtension_basic_facts : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧ (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧ (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧ (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧ (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧ Module.finrank F E = 2 := by sorry
