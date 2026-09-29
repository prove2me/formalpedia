-- Prove2me | Theorems.Thm_GaloisRep_tangentFinite_of_uniform_level
-- name    : GaloisRep.tangentFinite_of_uniform_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/7f53b3da-6fdc-528c-94b9-071724952db1
-- title:
--   Finite tangent space from a uniform level
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field $k=\mathrm{ResidueField}\,\mathcal{O}$ is finite, let $\bar\rho$ be a residual representation over $k$ (a two-dimensional $k$-vector space carrying a monoid homomorphism from $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})=\mathbb{\bar Q}\simeq_{\mathbb{Q}}\mathbb{\bar Q}$ to its $k$-endomorphisms which is trivial on the elements fixing some finite extension of $\mathbb{Q}$ inside $\bar{\mathbb{Q}}$), and let $\mathcal{D}$ be a predicate on the adic Galois representations $\rho$ over local $\mathcal{O}$-algebras $A$, that is, on free $A$-modules $V$ of rank $2$ with a monoid homomorphism $\rho$ to $\mathrm{End}_A V$ such that for every $n$ some finite extension of $\mathbb{Q}$ has the property that its fixing elements $\sigma$ satisfy $\rho(\sigma)v-v\in \mathfrak{m}_A^n V$ for all $v$. Assume there exists an intermediate field $M$ of $\bar{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that, with the dual numbers $k[\varepsilon]$ made an $\mathcal{O}$-algebra via $\mathcal{O}\to k\to k[\varepsilon]$ and $\mathrm{ResidueField}\,k[\varepsilon]$ a $k$-algebra via $k\to k[\varepsilon]\to\mathrm{ResidueField}\,k[\varepsilon]$, every adic representation $\rho$ over $k[\varepsilon]$ satisfying $\mathcal{D}$ whose residual representation (the base change of $V$ along $k[\varepsilon]\to\mathrm{ResidueField}\,k[\varepsilon]$) is isomorphic, compatibly with the Galois actions, to the base change of $\bar\rho$ to $\mathrm{ResidueField}\,k[\varepsilon]$ has $\rho(\sigma)=1$ for every $\sigma$ fixing $M$ pointwise. Then $\mathrm{TangentFinite}\,\mathcal{O}\,\bar\rho\,\mathcal{D}$ holds: the set of such $\rho$, taken modulo the relation of admitting a $k[\varepsilon]$-linear isomorphism intertwining the Galois actions, is finite.
--
--   This is the representation-theoretic half of the finiteness of the tangent space of a deformation condition (Mazur's $p$-finiteness condition), the finiteness being one of the hypotheses used in the representability of deformation problems; the arithmetic half is the production of a uniform level $M$ for conditions bounding ramification. It is cited by [`GaloisRep.tangentFinite_unramifiedOutside`](thm.html#GaloisRep.tangentFinite_unramifiedOutside).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_tangentFinite_of_uniform_level.lean

import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem GaloisRep.tangentFinite_of_uniform_level (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (hM : ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧
      letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
        ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
          (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
      letI : Algebra (ResidueField 𝒪) (ResidueField (DualNumber (ResidueField 𝒪))) :=
        ((IsLocalRing.residue (DualNumber (ResidueField 𝒪))).comp
          (algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪)))).toAlgebra
      ∀ ρ : GaloisRepAdic (DualNumber (ResidueField 𝒪)), 𝒟 ρ →
        ρ.residual.IsEquiv (ρbar.baseChange (ResidueField (DualNumber (ResidueField 𝒪)))) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ M, σ x = x) → ρ.ρ σ = 1) :
    TangentFinite 𝒪 ρbar 𝒟 := by sorry
