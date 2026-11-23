-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_isQuad_basic
-- name    : GlobalTheory.QNorm.isQuad_basic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:07.708556+00:00
-- url     : https://prove2.me/theorems/0cffaf8d-4158-45d4-a876-40919e5b6af0
-- title:
--   QNorm: is Quad basic
-- statement:
--   The QNorm construction uses the is Quad basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L72-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L72-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
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
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.isQuad_basic : ∀ (F E : Type) [Field F] [CharZero F] [Field E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧
    (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧
    (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧
    (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧
    (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧
    Module.finrank F E = 2 := by sorry
