-- Prove2me | Theorems.Thm_GlobalTheory_T_tensor_prime_over_ideal_completion
-- name    : GlobalTheory.T.tensor_prime_over_ideal_completion
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:37.142867+00:00
-- url     : https://prove2.me/theorems/283bf457-1fb3-50d0-a6f5-5b84e7e73034
-- title:
--   T: tensor prime over ideal completion
-- statement:
--   The T construction uses the tensor prime over ideal completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeOverIdealCompletionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeOverIdealCompletionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeOverIdealCompletion
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeOverIdealCompletionStatement
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

theorem GlobalTheory.T.tensor_prime_over_ideal_completion : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M), (∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈ LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C)) → ∀ Q₁ : Ideal (R ⊗[B] C), Q₁.IsPrime → I.map (algebraMap B R) ≤ Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) → ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by sorry
