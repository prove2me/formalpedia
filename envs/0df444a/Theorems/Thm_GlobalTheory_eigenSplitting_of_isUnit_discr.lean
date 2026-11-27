-- Prove2me | Theorems.Thm_GlobalTheory_eigenSplitting_of_isUnit_discr
-- name    : GlobalTheory.eigenSplitting_of_isUnit_discr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:22.667275+00:00
-- url     : https://prove2.me/theorems/3bc4dec6-1332-5c54-babb-ff5fed7b34cc
-- title:
--   Global Theory: eigen Splitting of is Unit discr
-- statement:
--   The Global Theory construction uses the eigen Splitting of is Unit discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L808-L857
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L808-L857

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open EigenSplit

theorem GlobalTheory.eigenSplitting_of_isUnit_discr {E : Type*} [Field E] [NumberField E]
    {R : Type*} [CommRing R] :
    (∀ (L : Type) [Field L] [CharZero L] [Algebra (𝓞 L) R] [Fintype (E →+* L)]
      [DecidableEq (E →+* L)], (∀ x : E, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits) →
      Fintype.card (E →+* L) = Module.finrank ℚ E ∧ Nonempty (Module.Basis (E →+* L) ℤ (𝓞 E)) ∧
        ∀ b : Module.Basis (E →+* L) ℤ (𝓞 E),
          (Matrix.of fun φ j => conjugateHom L R φ (b j)).det ^ 2 = (NumberField.discr E : R)) ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (σ : ι → 𝓞 E →+* R) (b : Module.Basis ι ℤ (𝓞 E)),
      (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R) →
      IsUnit (NumberField.discr E : R) →
      ∃ h : IsSplitting σ,
        (∃ e : 𝓞 E ⊗[ℤ] R ≃+* (ι → R), ∀ a r i, e (a ⊗ₜ r) i = σ i a * r) ∧
        CompleteOrthogonalIdempotents (idem h) ∧
        (∀ i, splitMap σ (idem h i) = Pi.single i 1) ∧
        ∀ (N : Type) [AddCommGroup N] [Module R N] (ρ : 𝓞 E →+* Module.End R N),
          (∀ i x, x ∈ eigenSub ρ (σ i) ↔ ∀ a, ρ a x = σ i a • x) ∧
          DirectSum.IsInternal (fun i => eigenSub ρ (σ i)) ∧
          (∀ i, LinearMap.IsProj (eigenSub ρ (σ i)) (tensorAction ρ (idem h i))) ∧
          (∀ (R' : Type) [CommRing R'] [Algebra R R'] (i : ι),
            eigenSub (baseChangeAction R' ρ) ((algebraMap R R').comp (σ i))
              = (eigenSub ρ (σ i)).baseChange R' ∧
            Function.Injective ((eigenSub ρ (σ i)).subtype.baseChange R')) ∧
          (∀ (N' N'' : Type) [AddCommGroup N'] [Module R N'] [AddCommGroup N''] [Module R N'']
            (ρ' : 𝓞 E →+* Module.End R N') (ρ'' : 𝓞 E →+* Module.End R N'')
            (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (hf : IsEquivariant ρ ρ' f)
            (hg : IsEquivariant ρ' ρ'' g), Function.Exact f g →
            ∀ i, Function.Exact (hf.eigenMap (σ i)) (hg.eigenMap (σ i))) ∧
          (Module.Finite R N → ∀ i, Module.Finite R (eigenSub ρ (σ i))) ∧
          (Module.Projective R N → ∀ i, Module.Projective R (eigenSub ρ (σ i))) ∧
          ∀ [Module.Free R N] [Module.Finite R N],
            ((∀ i, Module.Free R (eigenSub ρ (σ i))) → ∀ a, (ρ a).charpoly
              = ∏ i, (X - C (σ i a)) ^ Module.finrank R (eigenSub ρ (σ i))) ∧
            (IsLocalRing R → (∀ i, Module.Free R (eigenSub ρ (σ i))) ∧
              ∀ r : ι → ℕ, (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
                ∀ i, Module.finrank R (eigenSub ρ (σ i)) = r i) ∧
            ∀ r : ι → ℕ, (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
              ∀ (p : PrimeSpectrum R) i, Module.rankAtStalk (eigenSub ρ (σ i)) p = r i := by sorry
