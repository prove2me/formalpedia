-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt
-- name    : GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/ba85ada6-882b-507f-928a-76634d19b0c9
-- title:
--   Level-wise cotangent bound by the length of 𝒪/(q²-1)
-- statement:
--   Let $\mathcal{O}$ be a complete discrete valuation ring (a domain, discrete valuation ring, adically complete for its maximal ideal), let $\bar\rho$ be a two-dimensional residual Galois representation over the residue field of $\mathcal{O}$, and let $\mathcal{D}_0,\mathcal{D}'$ be deformation conditions on adic Galois representations over local $\mathcal{O}$-algebras, with $D_0$, $D'$ universal deformation data for $\bar\rho$ of type $\mathcal{D}_0$, $\mathcal{D}'$. Given $\mathcal{O}$-algebra maps $\theta : D'.R \to D_0.R$ and $x_0 : D_0.R \to \mathcal{O}$, local, with $\theta$ surjective and the base change of $D'.\rho$ along $\theta$ equivalent to $D_0.\rho$; primes $p \neq q$ with $p$ in the maximal ideal of $\mathcal{O}$; a valuation subring $P$ of $\overline{\mathbb{Q}}$ in which $q$ is a nonunit, an element $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and transitivity of the Galois action on the valuation subrings lying over $q$; the base change of $D'.\rho$ along $x_0 \circ \theta$ having characteristic polynomial $(X-1)^2$ on the inertia subgroup at every such valuation subring; every $\mathcal{D}'$-representation having cyclotomic determinant at $p$; $\mathcal{D}'$ stable under base change along local homomorphisms; every $\mathcal{D}'$-representation unipotent on inertia at $q$ being of type $\mathcal{D}_0$; and two tameness hypotheses on the inertia subgroup of $P$ relative to $\sigma$, $p$, $q$ (every $\tau$ in inertia satisfies $\sigma\tau\sigma^{-1}\tau^{-q} = w^{p^k}$ for some $w$ in inertia, and inertia is generated modulo $p^m$-th powers by one element) — then for every $n$, writing $I' = \ker(x_0 \circ \theta)$ and $I_0 = \ker x_0$, the $\mathcal{O}$-length of $\mathrm{Hom}_{\mathcal{O}}(I'/I'^2, \mathcal{O}/\mathfrak{m}^{n+1})$ modulo the functionals vanishing on the kernel of the induced map $I'/I'^2 \to I_0/I_0^2$ is at most the $\mathcal{O}$-length of $\mathcal{O}/(q^2-1)$.
--
--   This is the level-by-level form of the bound producing the factor $q^2-1$ that appears when the unipotent-inertia condition at an auxiliary prime $q$ is relaxed, measuring the cotangent discrepancy between the two deformation rings. It is the step invoked by the lemmas bounding the cotangent length of the relaxed deformation ring at an $\mathcal{O}$-point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.BilinearMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

theorem GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective (θ : D'.R →+* D₀.R))
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hconj : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P')
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪))
    (hur : (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsUnipotentOnInertiaAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsUnipotentOnInertiaAt q → 𝒟₀ ρA)
    (hdivI : ∀ (k : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ k) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ m : ℕ, ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        x ∈ P.inertiaSubgroupIn ℚ ∧ w ∈ P.inertiaSubgroupIn ℚ ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (n : ℕ) :
    Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) ⧸
      LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype)) ≤
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by sorry
