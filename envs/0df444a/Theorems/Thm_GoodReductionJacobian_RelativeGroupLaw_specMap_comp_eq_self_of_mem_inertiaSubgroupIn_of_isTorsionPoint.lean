-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint
-- name    : GoodReductionJacobian.RelativeGroupLaw.specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/491613c0-610b-5aa3-890c-b09c017373b9
-- title:
--   Inertia fixes n-torsion points when n is invertible
-- statement:
--   Let $R$ be a commutative local ring, $K$ a field that is an $R$-algebra, and $\Omega$ a field that is both an $R$-algebra and a $K$-algebra, these structures forming a scalar tower $R \to K \to \Omega$. Let $f : J \to \operatorname{Spec} R$ be a proper morphism of schemes and let $L$ be a relative group law on $f$, that is, a group structure on the set $\{\varphi : T \to J \mid \varphi \text{ followed by } f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} R$, with multiplication, unit and inverse satisfying the group axioms and compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} R$. Assume $L$ is commutative, in the sense that its multiplication on $T$-points is commutative for every $t : T \to \operatorname{Spec} R$. Let $n$ be a natural number whose image in $R$ is a unit, let $A \subseteq \Omega$ be a valuation subring containing the image of $R$ under the structure map, and let $\sigma$ be a $K$-algebra automorphism of $\Omega$ lying in `inertiaSubgroupIn`, the image in $\Omega \simeq_{\text{alg}[K]} \Omega$ of the inertia subgroup of $A$ over $K$ under the inclusion of the decomposition subgroup. Finally let $x$ be a morphism $\operatorname{Spec} \Omega \to J$ whose composite with $f$ is the structure morphism $\operatorname{Spec} \Omega \to \operatorname{Spec} R$, and suppose $x$ is $n$-torsion for $L$, i.e. the $n$-fold product $L$-product of $x$ with itself (defined by recursion, the empty product being the unit point) equals the unit $\Omega$-point. Then $\operatorname{Spec}(\sigma)$ followed by $x$ equals $x$.
--
--   This is the elementary direction of the criterion of Néron–Ogg–Shafarevich: torsion of order invertible on the base, on the generic fibre of a proper commutative group scheme over a local ring, is unramified. It is used for the Galois action on $\mathrm{Pic}^0$ of a smooth relative curve and for the Tate module of a fake elliptic curve in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint
    {R : Type u} [CommRing R] [IsLocalRing R]
    (K : Type u) [Field K] [Algebra R K]
    {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsProper f] (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hx : L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) n x) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by sorry
