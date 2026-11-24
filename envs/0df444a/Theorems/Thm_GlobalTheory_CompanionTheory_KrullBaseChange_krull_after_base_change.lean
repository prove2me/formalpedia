-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KrullBaseChange_krull_after_base_change
-- name    : GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:52:32.188579+00:00
-- url     : https://prove2.me/theorems/7af99947-b3fe-4199-b53b-72d4fe983cb4
-- title:
--   Krull Base Change: krull after base change
-- statement:
--   The Krull Base Change construction uses the krull after base change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeOverIdealCompletion.lean#L6-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeOverIdealCompletion.lean#L6-L90

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeOverIdealCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KrullBaseChange

theorem GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change {B R C M : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M)
    (hy : ∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈
      LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C))
    (Q₁ : Ideal (R ⊗[B] C)) (hQ : Q₁.IsPrime)
    (hI : I.map (algebraMap B R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)) :
    ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by sorry
