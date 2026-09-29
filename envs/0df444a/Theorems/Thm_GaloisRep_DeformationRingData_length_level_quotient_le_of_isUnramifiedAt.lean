-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt
-- name    : GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/fc939ce0-5282-5a26-9804-52ad331b7c48
-- title:
--   Level-wise relative cotangent bound at an auxiliary prime q
-- statement:
--   Let $\mathcal{O}$ be a complete discrete valuation ring (a domain, adically complete for its maximal ideal $\mathfrak{m}$), let $\bar\rho$ be a two-dimensional residual representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over the residue field of $\mathcal{O}$, and let $\mathcal{D}_0,\mathcal{D}'$ be deformation conditions on rank-two adic representations over local $\mathcal{O}$-algebras. Let $D_0$, $D'$ be corresponding deformation data: complete noetherian local $\mathcal{O}$-algebras $R_0=D_0.R$, $R'=D'.R$ with surjective residue map from $\mathcal{O}$, $\bar\rho$ absolutely irreducible, rank-two adic representations $\rho_0$, $\rho'$ of the respective types whose residual representations are equivalent to $\bar\rho$ base changed, and universal for these properties. Given $\mathcal{O}$-algebra maps $\theta:R'\to R_0$ and $x_0:R_0\to\mathcal{O}$, both local, with $\theta$ surjective and with $\rho'$ base changed along $\theta$ equivalent to $\rho_0$; primes $p\neq q$ with $p\in\mathfrak{m}$; a valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q\in P.\mathrm{nonunits}$, an element $\sigma$ of the decomposition group at $P$ acting as $x\mapsto x^q$ on the residue field of $P$, and all valuation subrings over $q$ conjugate to $P$ under $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; an element $a\in\mathcal{O}$ such that $\rho_0$ base changed along $x_0$ sends $\sigma$ to an endomorphism with characteristic polynomial $X^2-aX+q$, and is trivial on the inertia subgroup at every valuation subring over $q$. Assume further: every $\mathcal{D}'$-representation $\rho_A$ over $A$ satisfies $p\in\mathfrak{m}_A$ and $\det\rho_A(\sigma)-a\in(p^n)$ whenever $\sigma$ acts by $\mu\mapsto\mu^a$ on $p^n$-th roots of unity; $\mathcal{D}'$ is stable under base change along local homomorphisms; a $\mathcal{D}'$-representation trivial on all inertia subgroups over $q$ is of type $\mathcal{D}_0$; for each $k$ and each $\tau$ in the inertia subgroup $I_P$ there is $w\in I_P$ with $w^{p^k}=\sigma\tau\sigma^{-1}(\tau^q)^{-1}$; and for each $m$ there is $\gamma\in I_P$ such that every $\tau\in I_P$ is of the form $\gamma^j x^{p^m}w^{p^m}$ with $x,w\in I_P$. Then, for every $n$, writing $I=\ker(x_0\circ\theta)\subseteq R'$ and $J=\ker x_0\subseteq R_0$, the $\mathcal{O}$-length of $\mathrm{Hom}_{\mathcal{O}}(I/I^2,\mathcal{O}/\mathfrak{m}^{n+1})$ modulo the submodule of homomorphisms vanishing on the kernel of the induced map $I/I^2\to J/J^2$ is at most the $\mathcal{O}$-length of $\mathcal{O}/\big((q-1)(a^2-(q+1)^2)\big)$.
--
--   This is the local estimate at an auxiliary prime $q$ adjoined to the ramification set: it bounds, level by level, the part of the relative cotangent space of the relaxed deformation ring $R'$ at the $\mathcal{O}$-point $x_0\circ\theta$ that dies under $\theta$, by the length of $\mathcal{O}/((q-1)(a^2-(q+1)^2))$ built from the Frobenius trace $a$ at $q$. It feeds the two subsequent cotangent-length bounds used when comparing deformation rings of different types.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.lean

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

theorem GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnramifiedAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ q)
    (hconj : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P')
    (a : 𝒪)
    (hchar : (LinearMap.charpoly ((D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ)) =
      Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C ((q : 𝒪)))
    (hur : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsUnramifiedAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → (∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
        ∀ τ ∈ P'.inertiaSubgroupIn ℚ, ρA.ρ τ = 1) → 𝒟₀ ρA)
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
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {((q : 𝒪) - 1) * (a ^ 2 - ((q : 𝒪) + 1) ^ 2)}) := by sorry
