-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_subring_base_change_laws
-- name    : MazurTransfer.original_rational_subring_base_change_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T21:41:08.358638+00:00
-- url     : https://prove2.me/theorems/3227f692-b9db-44fc-ba4f-f938255ad730
-- statement:
--   The canonical original scalar base change of the same local Hopf algebra along the proved coefficient equivalence retains its given arithmetic labels, their original addition and Galois action compatibility, and at nineteen the original cyclotomic bialgebra classification and Cartier dual evaluation identity. All original hypotheses and complete propositions are retained. Named downstream consumer: normalization and torsor pushforward for the same selected integral pi quotient at nineteen.

import Definitions.Def_MazurTransfer_OriginalRationalSubringBaseChangeData20261020
import Theorems.Thm_MazurTransfer_original_hopf_base_change_arithmetic_points_laws
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_hopf_classification
noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13LocalRationalSubringEquivalence MazurTransfer.Order13RationalSubringBaseChange MazurTransfer.NineteenRootsGaloisRepresentation
open scoped TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringBaseChange
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.localSubringTower
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instFactPrimeOfNatNat_order13RationalSubringBaseChange
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.localSubringAlgebra
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringBaseChange
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringBaseChange

theorem MazurTransfer.original_rational_subring_base_change_laws : (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [aRK : Algebra (LocalRing q) K] [tRQ : IsScalarTower (LocalRing q) ℚ K] [aSK : Algebra (GaloisRep.ratLocalizedAt q) K] [tSQ : IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] {M : Type} (e : WithConv (H →ₐ[LocalRing q] K) ≃ M) [AddCommGroup M] (he_add : ∀ f g, e (f * g) = e f + e g), ∀ (f g : WithConv (GaloisRep.ratLocalizedAt q ⊗[LocalRing q] H →ₐ[GaloisRep.ratLocalizedAt q] K)),
baseChangeLabel q K e (f * g) = baseChangeLabel q K e f + baseChangeLabel q K e g) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [aRK : Algebra (LocalRing q) K] [tRQ : IsScalarTower (LocalRing q) ℚ K] [aSK : Algebra (GaloisRep.ratLocalizedAt q) K] [tSQ : IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] {M : Type} (e : WithConv (H →ₐ[LocalRing q] K) ≃ M) [AddCommGroup M] (ρ : (K ≃ₐ[ℚ] K) → M → M) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[LocalRing q] K)), (∀ x : H, g x = σ (f x)) → e g = ρ σ (e f)), ∀ (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (GaloisRep.ratLocalizedAt q ⊗[LocalRing q] H →ₐ[GaloisRep.ratLocalizedAt q] K))
    (hfg : ∀ x, g x = σ (f x)),
baseChangeLabel q K e g = ρ σ (baseChangeLabel q K e f)) ∧ (∀ (G : Type) [CommRing G] [HopfAlgebra R G] [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G] (label : WithConv (G →ₐ[R] F) ≃ Additive (Roots F)) (hadd : ∀ f g, label (f * g) = label f + label g) (hact : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (G →ₐ[R] F)), (∀ x : G, g x = σ (f x)) → label g = rootsRepresentation F σ (label f)), ∃ φ : (S ⊗[R] G) ≃ₐc[S]
      MonoidAlgebra S (WithConv (CartierDual S (S ⊗[R] G) →ₐ[S] F)),
      ∀ (ψ : WithConv (CartierDual S (S ⊗[R] G) →ₐ[S] F)) (θ : CartierDual S (S ⊗[R] G)),
        algebraMap S F (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ) := by sorry
