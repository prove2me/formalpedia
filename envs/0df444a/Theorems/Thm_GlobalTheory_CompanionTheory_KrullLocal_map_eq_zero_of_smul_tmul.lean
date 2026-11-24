-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KrullLocal_map_eq_zero_of_smul_tmul
-- name    : GlobalTheory.CompanionTheory.KrullLocal.map_eq_zero_of_smul_tmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:52:35.830184+00:00
-- url     : https://prove2.me/theorems/865590f5-fa81-43d6-b14b-a0c576dd763e
-- title:
--   Krull Local: map eq zero of smul tmul
-- statement:
--   The Krull Local construction uses the map eq zero of smul tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeLocalizationCriterion.lean#L128-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeLocalizationCriterion.lean#L128-L210

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KrullLocal

theorem GlobalTheory.CompanionTheory.KrullLocal.map_eq_zero_of_smul_tmul {B R C M D N : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [CommRing D] [Algebra R D]
    [AddCommGroup N] [Module R N] [Module D N] [IsScalarTower R D N]
    (J : Ideal B) (hJ : ∀ a ∈ J, algebraMap R D (algebraMap B R a) = 0)
    (Q₀ : Ideal (R ⊗[B] C)) (hQ : Q₀.IsPrime)
    (hunit : ∀ r : R, r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) →
      IsUnit (algebraMap R D r))
    (h1 : ∀ c : C, ∃ b t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * algebraMap B C b = 0) → ∃ t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      t * b ∈ J)
    (ι : M →ₗ[R] N) (y : M) (w : R ⊗[B] C) (hw0 : w ∉ Q₀)
    (hw : w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0) : ι y = 0 := by sorry
