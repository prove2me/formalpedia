-- Prove2me | Theorems.Thm_GlobalTheory_T_tensor_prime_localization_criterion
-- name    : GlobalTheory.T.tensor_prime_localization_criterion
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:32.663375+00:00
-- url     : https://prove2.me/theorems/b8952529-d0bb-54aa-bd05-dc4f61bfd86a
-- title:
--   T: tensor prime localization criterion
-- statement:
--   The T construction uses the tensor prime localization criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeLocalizationCriterionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeLocalizationCriterionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tensor_prime_localization_criterion : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] (J : Ideal B), (∀ a ∈ J, ∀ m : M, a • m = 0) → ∀ Q₀ : Ideal (R ⊗[B] C), Q₀.IsPrime → (∀ c : C, ∃ b t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * (algebraMap B C t * c) = v * algebraMap B C b) → (∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * algebraMap B C b = 0) → ∃ t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ t * b ∈ J) → ∀ (y : M) (w : R ⊗[B] C), w ∉ Q₀ → w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 → ∃ u : R, u ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ∧ u • y = 0 := by sorry
