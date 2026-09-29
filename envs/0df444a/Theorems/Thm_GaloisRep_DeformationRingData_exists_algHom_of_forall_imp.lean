-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_exists_algHom_of_forall_imp
-- name    : GaloisRep.DeformationRingData.exists_algHom_of_forall_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/dd05605a-05f9-5640-a997-5b7c4dd5bec5
-- title:
--   Functoriality of deformation ring data under implication of conditions
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring that is a domain and is complete for the adic topology of its maximal ideal, and let $\bar\rho$ be a residual representation over the residue field $k=\mathcal{O}/\mathfrak{m}_{\mathcal{O}}$, that is, a two-dimensional $k$-vector space with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ into its endomorphism ring which becomes trivial on the subgroup fixing some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Let $\mathcal{D}_0$ and $\mathcal{D}'$ be two predicates, each assigning to every local $\mathcal{O}$-algebra $A$ and every adically continuous representation $\rho$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on a free $A$-module of rank $2$ a proposition, and assume that for all such $A$ and $\rho$, $\mathcal{D}_0\,\rho$ implies $\mathcal{D}'\,\rho$. Let $D_0$ and $D'$ be deformation ring data for $\bar\rho$ over $\mathcal{O}$ for the conditions $\mathcal{D}_0$ and $\mathcal{D}'$ respectively: each consists of a complete noetherian local $\mathcal{O}$-algebra $R$ whose structure map is local and induces a surjection onto the residue field of $R$, a representation $\rho$ over $R$ satisfying the condition, an equivalence of its residual representation with the base change of $\bar\rho$, and the universal property expressing that any representation of that type over such an algebra, with the same residual class, arises by base change along a unique local $\mathcal{O}$-algebra map from $R$. The conclusion asserts the existence of an $\mathcal{O}$-algebra homomorphism $\theta : D'.R \to D_0.R$, together with the fact that it is a local homomorphism, such that the base change of $D'.\rho$ along $\theta$, namely $D_0.R \otimes_{D'.R} D'.\rho.V$ with the induced Galois action, admits a $D_0.R$-linear Galois-equivariant isomorphism onto $D_0.\rho.V$; uniqueness of $\theta$ is not part of the statement.
--
--   This is the functoriality of universal deformation rings with respect to implication between deformation conditions: a stricter condition yields a ring receiving a map from the ring for the looser condition, compatibly with the universal deformations. It is used in the construction of the patching data and in the comparison of deformation rings with Hecke algebras, where the deformation conditions vary along the level-changing arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_exists_algHom_of_forall_imp.lean

import Definitions.Def_GaloisRep_DeformationRingData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.DeformationRingData.exists_algHom_of_forall_imp
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic A → Prop}
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
      (ρ : GaloisRepAdic A), 𝒟₀ ρ → 𝒟' ρ)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀)
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟') :
    ∃ θ : D'.R →ₐ[𝒪] D₀.R, ∃ hθ : IsLocalHom (θ : D'.R →+* D₀.R),
      (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ := by sorry
