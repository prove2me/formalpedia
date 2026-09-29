-- Prove2me | Theorems.Thm_GaloisRep_algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy
-- name    : GaloisRep.algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/0450aca0-bc8e-5815-97e7-01e81d17fc4d
-- title:
--   Uniqueness of the classifying map of a type-D lift
-- statement:
--   Let $\mathcal{O}$ be a local ring with finite residue field $k=\mathrm{ResidueField}\,\mathcal{O}$, let $\bar\rho$ be a residual Galois representation over $k$ (a $k$-vector space $V$ of dimension $2$ together with a homomorphism from $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$, realised as $\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$, to $\mathrm{End}_k V$ that is trivial on the pointwise stabiliser of some finite extension of $\mathbb{Q}$), and let $\mathcal{D}$ be a predicate on rank-two adic Galois representations over local $\mathcal{O}$-algebras satisfying [`GaloisRep.IsDeformationCondition`](def/GaloisRep_DeformationCondition.html#L19). Let $\rho_0$ be a continuous homomorphism from the Galois group to $\mathrm{GL}_2$ of the residue field of $\mathcal{O}$ viewed as a pro-Artinian $\mathcal{O}$-algebra, and $b$ a basis of $V$ with $\rho_0(\sigma)$ the matrix of $\bar\rho(\sigma)$ in $b$ for all $\sigma$; assume the associated matrix representation of $\rho_0$ is absolutely irreducible, i.e. remains irreducible after every field base change. Let $R$ be a pro-Artinian local $\mathcal{O}$-algebra whose topology is the $\mathfrak{m}_R$-adic one, and let $e$ exhibit $R$ as corepresenting the functor sending a pro-Artinian $\mathcal{O}$-algebra $S$ to the image in the quotient functor (orbits under conjugation by elements of $\mathrm{GL}_2(S)$ trivial modulo $\mathfrak{m}_S$) of the set of lifts $\rho'$ of $\rho_0$ to $\mathrm{GL}_2(S)$ such that every pushforward of $\rho'$ to an Artinian quotient realises, in some basis, a representation satisfying $\mathcal{D}$. Let $\rho^{\mathrm{u}}:\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})\to\mathrm{GL}_2(R)$ be continuous, lie in that set of conditioned lifts at $R$, and have class equal to the universal element $e(\mathrm{id}_R)$; let `hcont` record adic continuity of the resulting action on $R^2$. Let $A$ be a Noetherian local $\mathcal{O}$-algebra, $\mathfrak{m}_A$-adically complete, with local structure map whose composite with the residue map is surjective, and let $\rho_A$ be a rank-two adic Galois representation over $A$ with $\mathcal{D}\rho_A$. Then any two local $\mathcal{O}$-algebra homomorphisms $\varphi,\varphi':R\to A$ for which the base changes along $\varphi$ and along $\varphi'$ of the representation $R^2$ attached to $\rho^{\mathrm{u}}$ are each $A$-linearly isomorphic to $\rho_A$ by a Galois-equivariant isomorphism are equal.
--
--   This is the uniqueness half of the universal property of the deformation ring of $\bar\rho$ with deformation condition $\mathcal{D}$: a representation of type $\mathcal{D}$ over a complete Noetherian local $\mathcal{O}$-algebra is induced from the universal lift by at most one local $\mathcal{O}$-algebra homomorphism. It feeds into [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData), where the existence and uniqueness halves are packaged together.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory IsLocalRing

theorem GaloisRep.algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    [Representation.IsAbsolutelyIrreducible.{0} (Deformation.matrixRepresentation ρ₀.toMonoidHom)]
    {R : Deformation.ProartinianCat 𝒪} [IsLocalRing.IsAdicTopology R]
    (e : (Deformation.conjQuotSubfunctor (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.CorepresentableBy R)
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).obj R)
    (hρu' : (Quotient.mk'' ρu : (Deformation.repnQuotFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj R) = (e.homEquiv (𝟙 R)).1)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom)))
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hresA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (ρA : GaloisRepAdic A) (hDA : 𝒟 ρA)
    (φ φ' : R →ₐ[𝒪] A) (hφ : IsLocalHom (φ : R →+* A)) (hφ' : IsLocalHom (φ' : R →+* A))
    (h : (GaloisRepAdic.baseChangeAlong (φ : R →+* A) hφ
        { V := Fin 2 → R, finrank_eq := by simp,
          ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
          isAdicContinuous := hcont }).IsEquiv ρA)
    (h' : (GaloisRepAdic.baseChangeAlong (φ' : R →+* A) hφ'
        { V := Fin 2 → R, finrank_eq := by simp,
          ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
          isAdicContinuous := hcont }).IsEquiv ρA) :
    φ = φ' := by sorry
