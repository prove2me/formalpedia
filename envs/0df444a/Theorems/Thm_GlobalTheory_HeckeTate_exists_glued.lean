-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_exists_glued
-- name    : GlobalTheory.HeckeTate.exists_glued
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:54.272904+00:00
-- url     : https://prove2.me/theorems/988177aa-c502-44c1-ac2c-3da4f2bfdb13
-- title:
--   Hecke Tate: exists glued
-- statement:
--   The Hecke Tate construction uses the exists glued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L153-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L153-L325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}

theorem GlobalTheory.HeckeTate.exists_glued [IsDedekindDomain R] [CharZero R] (h : IsUnimod σ B) (h' : IsUnimod σ B')
    (hσ : ∀ a, σ (σ a) = a) {P : Ideal R} (hP : P.IsMaximal) (hPP : P ⊔ P.map (σ : R →+* R) = ⊤)
    {p : ℕ} (hp0 : p ≠ 0) (hpP : (p : R) ∈ P) (i : M' →ₗ[R] M) (hi : Function.Injective i)
    (hB : ∀ x y, B (i x) (i y) = (p : ℤ) ^ 2 * B' x y)
    (hsq : ∀ a, ∃ y, i y = (p : R) ^ 2 • a) (hlow : ∀ γ ∈ P, ∀ a, ∃ y, i y = (γ * p) • a)
    (φ : M →ₗ[R] M') (φ' : M' →ₗ[R] M) {s : R} (hs : s ∉ P) (hφ : ∀ a, φ' (φ a) = s • a)
    (hφ' : ∀ y, φ (φ' y) = s • y) :
    ∃ G : ℕ → M →ₗ[R] M',
      (∀ n : ℕ, 0 < n → ∀ a, G n a ∈ mults M' (n : R) → a ∈ mults M (n : R)) ∧
      (∀ n : ℕ, 0 < n → ∀ y, ∃ a, G n a - y ∈ mults M' (n : R)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, G (n * m) a - G n a ∈ mults M' (n : R)) ∧
      (∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ B' (G n a) (G n b) - B a b) ∧
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ a, i (G n a) - (p : R) • a ∈ mults M (n : R)) := by sorry
