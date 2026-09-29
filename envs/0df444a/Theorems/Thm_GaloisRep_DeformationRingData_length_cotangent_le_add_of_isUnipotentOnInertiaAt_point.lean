-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_length_cotangent_le_add_of_isUnipotentOnInertiaAt_point
-- name    : GaloisRep.DeformationRingData.length_cotangent_le_add_of_isUnipotentOnInertiaAt_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/5042fc8c-41c6-5795-b74e-b71cc91c184a
-- title:
--   Cotangent bound ≤ length of 𝒪/(q²-1) when unipotency at q is relaxed
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring (a domain, discrete valuation ring, adically complete for its maximal ideal) and $\bar\rho$ a two-dimensional representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over the residue field of $\mathcal O$ factoring through a finite level. Let $\mathcal D_0,\mathcal D'$ be predicates on two-dimensional adically continuous Galois representations over local $\mathcal O$-algebras, and let $D_0$, $D'$ be `DeformationRingData` for $\bar\rho$ with respect to $\mathcal D_0$, $\mathcal D'$: that is, complete noetherian local $\mathcal O$-algebras $R_0=D_0.R$, $R'=D'.R$ with residually surjective structure map, together with representations of the given type whose residual representation recovers $\bar\rho$ and which are universal among such deformations (with $\bar\rho$ absolutely irreducible). Given $\mathcal O$-algebra maps $\theta\colon R'\to R_0$ and $x_0\colon R_0\to\mathcal O$, primes $p\neq q$ with $p$ in the maximal ideal of $\mathcal O$, the hypotheses are: $\theta$ and $x_0$ are local, so is $x_0\circ\theta$, $\theta$ is surjective, the base change of $D'.\rho$ along $\theta$ is equivalent to $D_0.\rho$, the specialisation of $D'.\rho$ along $x_0\circ\theta$ has $\mathrm{charpoly}=(X-1)^2$ on every inertia subgroup at every valuation subring of $\overline{\mathbb Q}$ lying over $q$; moreover every representation of type $\mathcal D'$ has cyclotomic determinant at $p$ in the sense of `DetIsCyclotomic`, $\mathcal D'$ is stable under base change along local ring maps, and a representation of type $\mathcal D'$ with unipotent inertia at $q$ is of type $\mathcal D_0$. Then $\mathrm{length}_{\mathcal O}$ of the cotangent module $\ker(x_0\circ\theta)/\ker(x_0\circ\theta)^2$ is at most $\mathrm{length}_{\mathcal O}\bigl(\ker x_0/(\ker x_0)^2\bigr)+\mathrm{length}_{\mathcal O}\bigl(\mathcal O/(q^2-1)\bigr)$.
--
--   This is the local bound at a prime $q$ for one rung of the level-raising ladder in the modularity lifting argument: relaxing the condition of unipotent inertia at $q$ increases the length of the cotangent module of the point $x_0$ by at most $\mathrm{length}_{\mathcal O}(\mathcal O/(q^2-1))$, for arbitrary side conditions at $p$ encoded by $\mathcal D'$. It is used in the construction of patching data for residually modular representations, including at rungs where the two deformation conditions agree, since only an upper bound for the growth is asserted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_length_cotangent_le_add_of_isUnipotentOnInertiaAt_point.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem GaloisRep.DeformationRingData.length_cotangent_le_add_of_isUnipotentOnInertiaAt_point
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
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪))
    (hur : (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsUnipotentOnInertiaAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsUnipotentOnInertiaAt q → 𝒟₀ ρA) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent +
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by sorry
