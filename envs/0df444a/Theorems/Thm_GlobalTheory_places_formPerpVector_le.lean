-- Prove2me | Theorems.Thm_GlobalTheory_places_formPerpVector_le
-- name    : GlobalTheory.places_formPerpVector_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:27.740896+00:00
-- url     : https://prove2.me/theorems/bf2024bd-0caa-568f-a157-1b11d7cb5a75
-- title:
--   Global Theory: places form Perp Vector le
-- statement:
--   The Global Theory construction uses the places form Perp Vector le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L384-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L384-L449

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
variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

theorem GlobalTheory.places_formPerpVector_le [Fintype T] {p : ℕ} (h : M →ₗ[R] M →ₗ⋆[R] R)
    (hh : ∀ u v, h u v = star (h v u)) (τ : T → R →+* ℂ)
    (hτ : ∀ t x, τ t (star x) = starRingEnd ℂ (τ t x)) (hpos : ∀ t v, 0 ≤ (τ t (h v v)).re)
    (e e' : Fin p → M) (g : M) {r : ℝ}
    (he : ∀ a, √(∑ t, (τ t (h (e a) (e a))).re) ≤ r)
    (he' : ∀ a, √(∑ t, (τ t (h (e' a) (e' a))).re) ≤ r)
    (hg : √(∑ t, (τ t (h g g)).re) ≤ r) :
    (∀ t, ‖τ t (formPairMatrix h e e').det‖ ≤ p ! * r ^ (2 * p)) ∧
      √(∑ t, (τ t (h (formPerpVector h e e' g) (formPerpVector h e e' g))).re)
        ≤ (p + 1)! * r ^ (2 * p + 1) := by sorry
