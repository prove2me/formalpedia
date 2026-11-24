-- Prove2me | Theorems.Thm_GlobalTheory_exists_free_complex
-- name    : GlobalTheory.exists_free_complex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:02.886265+00:00
-- url     : https://prove2.me/theorems/71165cdf-59e6-4901-8410-5841d839e9c1
-- title:
--   Global Theory: exists free complex
-- statement:
--   The Global Theory construction uses the exists free complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L299-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L299-L342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem GlobalTheory.exists_free_complex (n : ℕ) : ∀ (C : ℕ → ModuleCat.{v} R)
    (d : ∀ p, C p →ₗ[R] C (p + 1)) (B : Submodule R (C 0))
    (_ : ∀ p, n ≤ p → Subsingleton (C p))
    (_ : Module.Finite R (LinearMap.ker (d 0) ⧸ B.comap (LinearMap.ker (d 0)).subtype))
    (_ : ∀ p, Module.Finite R (LinearMap.ker (d (p + 1)) ⧸
      (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)),
    ∃ (m : ℕ → ℕ) (δ : ∀ p, (Fin (m p) → R) →ₗ[R] (Fin (m (p + 1)) → R))
      (φ : ∀ p, (Fin (m p) → R) →ₗ[R] C p),
      (∀ p, n ≤ p → m p = 0) ∧ (∀ p x, δ (p + 1) (δ p x) = 0) ∧
      (∀ p x, d p (φ p x) = φ (p + 1) (δ p x)) ∧
      (∀ c k, d 0 c = φ 1 k → δ 1 k = 0 → ∃ x, c - φ 0 x ∈ B ∧ δ 0 x = k) ∧
      ∀ p c k, d (p + 1) c = φ (p + 2) k → δ (p + 2) k = 0 →
        ∃ c' k', d p c' + φ (p + 1) k' = c ∧ δ (p + 1) k' = k := by sorry
