-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine
-- name    : GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/0ae01690-57df-59f4-8712-954404f58be3
-- title:
--   A local invariant killed by α²-1 on ordinary lines
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain, complete for its maximal ideal $\mathfrak{m}$, let $\bar\rho$ be a residual Galois representation over the residue field of $\mathcal{O}$ (a two-dimensional representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ factoring through a finite level), and let $\mathcal{D}_0,\mathcal{D}'$ be deformation conditions, i.e. predicates on adic Galois representations over local $\mathcal{O}$-algebras. Given universal data $D_0$, $D'$ for $\bar\rho$ of types $\mathcal{D}_0$, $\mathcal{D}'$ with rings $R_0=D_0.R$, $R'=D'.R$, an $\mathcal{O}$-algebra map $\theta : R' \to R_0$ and an $\mathcal{O}$-point $x_0 : R_0 \to \mathcal{O}$, a prime $p \neq 2$ with $p \in \mathfrak{m}$, assume: $\theta$ and $x_0$ are local homomorphisms, $\theta$ is surjective, the base change $\rho_{x_0}$ of $D_0.\rho$ along $x_0$ is flat at $p$ in the sense of [`GaloisRepAdic.IsFlatAt`](def/GaloisRep_Flat.html#L29), and the base change of $D'.\rho$ along $\theta$ is equivalent to $D_0.\rho$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P$, let $V$ be the underlying module of $\rho_{x_0}$ and $L \subseteq V$ a submodule of the form $\mathcal{O}\cdot b_0$ for some basis $b$ of $V$ indexed by $\mathrm{Fin}\,2$, stable under the decomposition subgroup of $P$ over $\mathbb{Q}$, with the inertia subgroup (as a subgroup of the absolute Galois group) acting trivially on $V/L$, and let $\alpha \in \mathcal{O}$ be such that every $\sigma$ in the decomposition subgroup which is a Frobenius at $p$ for $P$ satisfies $\rho_{x_0}(\sigma)v - \alpha v \in L$ for all $v$; assume $\alpha^2 - 1 \neq 0$. Assume further that every representation of type $\mathcal{D}'$ has cyclotomic determinant at $p$, that $\mathcal{D}'$ is stable under base change along local homomorphisms of local $\mathcal{O}$-algebras, that $\mathcal{D}'$ implies ordinarity at $p$ (existence, at every place over $p$, of such a line $L$), and that $\mathcal{D}'$ together with flatness at $p$ implies $\mathcal{D}_0$. Then for every $n$ there is an $\mathcal{O}$-linear functional
--   $$y : \mathrm{Hom}_{\mathcal{O}}\big(\mathrm{Cot}(\ker(x_0 \circ \theta)),\, \mathcal{O}/\mathfrak{m}^{n+1}\big) \longrightarrow \mathcal{O}/\mathfrak{m}^{n+1}$$
--   on the module of homomorphisms from the cotangent module $I/I^2$ of $I = \ker(x_0 \circ \theta)$, such that $(\alpha^2-1)\cdot y(\varphi) = 0$ for all $\varphi$, and such that $y(\varphi) = 0$ forces $\varphi$ to vanish on the kernel of the map $\mathrm{Cot}(\ker(x_0\circ\theta)) \to \mathrm{Cot}(\ker x_0)$ induced by $\theta$.
--
--   This is the local input at $p$ to the comparison of the two deformation rings $R'$ and $R_0$ at the $\mathcal{O}$-point $x_0$: a first-order deformation of $\rho_{x_0}$ that is not detected by the invariant $y$ is flat at $p$, hence of type $\mathcal{D}_0$, and the annihilation of $y$ by $\alpha^2-1$ measures the failure by a bounded amount. It is the substance of the per-level estimate [`GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine`](thm.html#GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine), which deduces a length bound from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.BilinearMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hfl : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsFlatAt p)
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (L : Submodule 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V, L = 𝒪 ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - v ∈ L)
    (α : 𝒪)
    (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p →
      ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
        (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - α • v ∈ L)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (Hord : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsOrdinaryAt p)
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsFlatAt p → 𝒟₀ ρA)
    (hα1 : α ^ 2 - 1 ≠ 0) (n : ℕ) :
    ∃ y : ((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1),
      (∀ φ, (α ^ 2 - 1) • y φ = 0) ∧
      ∀ φ, y φ = 0 → φ ∈ LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype) := by sorry
