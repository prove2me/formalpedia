-- Prove2me | Theorems.Thm_GlobalTheory_HermitianGauss_gauss_fin
-- name    : GlobalTheory.HermitianGauss.gauss_fin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:06.362062+00:00
-- url     : https://prove2.me/theorems/4b8a3c35-1f53-479b-91cb-a76595924312
-- title:
--   Hermitian Gauss: gauss fin
-- statement:
--   The Hermitian Gauss construction uses the gauss fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L243-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L243-L454

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
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
variable {σ : R →+* R} {β : M → M → ℂ}

theorem GlobalTheory.HermitianGauss.gauss_fin {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1) {lam : ℕ →* ℂ} (hlam : GoodNorm σ lam)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (h0 : ∀ y, β 0 y = 1) (n : ℕ) :
    ∀ B C : Submodule R M, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → (pts B).card = n * (pts C).card →
      ∑ y ∈ pts B, β (w • y) y = (pts C).card * lam n ∧ lam n ^ 2 = n := by sorry
