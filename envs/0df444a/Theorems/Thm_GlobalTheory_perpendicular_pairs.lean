-- Prove2me | Theorems.Thm_GlobalTheory_perpendicular_pairs
-- name    : GlobalTheory.perpendicular_pairs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:36.847043+00:00
-- url     : https://prove2.me/theorems/c152b194-355e-4600-adbf-08218b884126
-- title:
--   Global Theory: perpendicular pairs
-- statement:
--   The Global Theory construction uses the perpendicular pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L453-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L453-L471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory

theorem GlobalTheory.perpendicular_pairs {p q : ℕ} :
    (∀ {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
      (h : M →ₗ[R] M →ₗ⋆[R] R) (e e' : Fin p → M) (g : Fin q → M),
      (∀ b c, h (formPerpVector h e e' (g b)) (e c) = 0) ∧
      (∀ (A : Subring R) (L : Submodule A M), (∀ a, e' a ∈ L) → (∀ b, g b ∈ L) →
        (∀ a a', h (e' a') (e a) ∈ A) → (∀ b a, h (g b) (e a) ∈ A) →
        ∀ b, formPerpVector h e e' (g b) ∈ L) ∧
      (∀ b, (∀ a, h (g b) (e a) = 0) →
        formPerpVector h e e' (g b) = (formPairMatrix h e e').det • g b)) ∧
    (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (e e' : Fin p → V) (g : Fin q → V) (r : ℝ),
      (∀ a, ‖e a‖ ≤ r) → (∀ a, ‖e' a‖ ≤ r) → (∀ b, ‖g b‖ ≤ r) →
      ‖(formPairMatrix (innerFormLeft V) e e').det‖ ≤ p ! * r ^ (2 * p) ∧
      ∀ b, ‖formPerpVector (innerFormLeft V) e e' (g b)‖ ≤ (p + 1)! * r ^ (2 * p + 1)) := by sorry
