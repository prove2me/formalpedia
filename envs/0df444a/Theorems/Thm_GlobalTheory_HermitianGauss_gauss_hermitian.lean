-- Prove2me | Theorems.Thm_GlobalTheory_HermitianGauss_gauss_hermitian
-- name    : GlobalTheory.HermitianGauss.gauss_hermitian
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:18.353807+00:00
-- url     : https://prove2.me/theorems/aa4e4e83-a180-4883-8183-19efc614fd62
-- title:
--   Hermitian Gauss: gauss hermitian
-- statement:
--   The Hermitian Gauss construction uses the gauss hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L458-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L458-L561

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss

theorem GlobalTheory.HermitianGauss.gauss_hermitian : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by sorry
