-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv
-- name    : GaloisRep.DeformationRingData.algHom_eq_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/68b370b3-3781-5c07-b7b2-56686e5636f6
-- title:
--   Uniqueness of classifying maps out of a deformation ring
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain that is complete for the adic topology of its maximal ideal, let $\bar\rho$ be a residual Galois representation over the residue field of $\mathcal{O}$ — a two-dimensional module with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-automorphisms of `AlgebraicClosure ℚ`, into its endomorphism ring, trivial on the automorphisms fixing some finite extension of $\mathbb{Q}$ — and let $\mathcal{D}$ be a predicate on adically continuous two-dimensional free representations over local $\mathcal{O}$-algebras. Let $D$ be a [`GaloisRep.DeformationRingData`](def/GaloisRep_DeformationRingData.html#L8) for $(\mathcal{O},\bar\rho,\mathcal{D})$: a noetherian local $\mathcal{O}$-algebra $R = D.R$, complete for its maximal-ideal topology, with local structure map inducing a surjection onto the residue field of $R$, together with $\bar\rho$ absolutely irreducible, a representation $D.\rho$ over $R$ satisfying $\mathcal{D}$ whose residual representation is equivalent to the base change of $\bar\rho$ along the induced map of residue fields, and the universal property that every such datum over a target is classified by a unique local $\mathcal{O}$-algebra map. Now let $A$ be a noetherian local $\mathcal{O}$-algebra, complete for its maximal-ideal topology, with local structure map whose composite with the residue map of $A$ is surjective, let $\rho_A$ be a representation over $A$ satisfying $\mathcal{D}$ whose residual representation is equivalent to the base change of $\bar\rho$ along the map of residue fields induced by $\mathcal{O} \to A$, and let $\varphi_1,\varphi_2 : R \to A$ be $\mathcal{O}$-algebra maps that are local homomorphisms and such that the base change of $D.\rho$ along each is equivalent (via an $A$-linear isomorphism commuting with the Galois actions) to $\rho_A$. Then $\varphi_1 = \varphi_2$.
--
--   This is the uniqueness half of the universal property of a deformation ring, extracted as a standalone cancellation lemma: any two local $\mathcal{O}$-algebra maps inducing the same lift of $\bar\rho$ up to equivalence coincide. It is used repeatedly in the construction of patching data and in the comparison of deformation rings with Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv.lean

import Definitions.Def_GaloisRep_DeformationRingData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.DeformationRingData.algHom_eq_of_isEquiv
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (ρA : GaloisRepAdic A) (hρA : 𝒟 ρA)
    (hres : ρA.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A))))
    (φ₁ φ₂ : D.R →ₐ[𝒪] A) (h₁ : IsLocalHom (φ₁ : D.R →+* A)) (h₂ : IsLocalHom (φ₂ : D.R →+* A))
    (e₁ : (D.ρ.baseChangeAlong (φ₁ : D.R →+* A) h₁).IsEquiv ρA)
    (e₂ : (D.ρ.baseChangeAlong (φ₂ : D.R →+* A) h₂).IsEquiv ρA) :
    φ₁ = φ₂ := by sorry
