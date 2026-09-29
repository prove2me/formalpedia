-- Prove2me | Theorems.Thm_GaloisRep_tangentFinite_of_imp
-- name    : GaloisRep.tangentFinite_of_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/a3cc6e31-4455-518b-a243-1832fbc11b4a
-- title:
--   Tangent finiteness passes to smaller deformation conditions
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring and let $\bar\rho$ be a residual representation over its residue field, that is, a two-dimensional $\mathrm{ResidueField}\,\mathcal{O}$-vector space carrying a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to its endomorphism ring which becomes trivial on the automorphisms fixing some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Let $\mathcal{D}$ and $\mathcal{D}'$ be two predicates on objects of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), uniformly in local commutative $\mathcal{O}$-algebras $A$, where an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) is a finite free $A$-module of rank $2$ with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to its $A$-endomorphisms such that for every $n$ there is a finite extension $L/\mathbb{Q}$ in $\overline{\mathbb{Q}}$ with $\rho(\sigma)v-v \in \mathfrak{m}_A^n V$ for all $\sigma$ fixing $L$ pointwise and all $v$. Assume $\mathcal{D}\rho$ implies $\mathcal{D}'\rho$ for all such $A$ and $\rho$, and assume `TangentFinite 𝒪 ρbar 𝒟'`: the set of representations over the dual numbers $\mathrm{ResidueField}\,\mathcal{O}[\varepsilon]$ (an $\mathcal{O}$-algebra through the residue map) satisfying $\mathcal{D}'$ and whose residual representation is isomorphic to the base change of $\bar\rho$, taken up to $A$-linear Galois-equivariant isomorphism, is finite. Then the same finiteness holds for $\mathcal{D}$.
--
--   The tangent space of a deformation problem is its set of deformations to the dual numbers; this is the monotonicity of the finiteness of that set in the deformation condition. It serves as an input to the construction of deformation ring data, where tangent finiteness for the ordinary, strictly ordinary and flat conditions combined with unipotence on inertia is deduced from the finiteness for a weaker condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_tangentFinite_of_imp.lean

import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem GaloisRep.tangentFinite_of_imp (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A), 𝒟 ρ → 𝒟' ρ)
    (hfin : TangentFinite 𝒪 ρbar 𝒟') : TangentFinite 𝒪 ρbar 𝒟 := by sorry
