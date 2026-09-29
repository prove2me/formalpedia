-- Prove2me | Theorems.Thm_Module_exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation
-- name    : Module.exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/1bd2aa59-1315-5722-8c34-b2337b9357c8
-- title:
--   Generic fibre of a faithful module with a quadratic relation
-- statement:
--   Let $\mathcal O$ be a commutative domain of characteristic zero, $R$ a reduced commutative $\mathcal O$-algebra that is finite as an $\mathcal O$-module, $G$ a group, and $Y$ an additive group carrying compatible $R$- and $\mathcal O$-module structures (scalar tower over $\mathcal O$), finite and torsion-free as an $\mathcal O$-module, on which $R$ acts faithfully in the sense that $x\in R$ with $x\cdot y=0$ for all $y\in Y$ forces $x=0$. Let $\rho_Y\colon G\to \mathrm{End}_R(Y)$ be a monoid homomorphism, $\Delta$ a finite commutative group, $D\colon\Delta\to\mathrm{End}_R(Y)$ a homomorphism whose values commute with every $\rho_Y(g)$, and let $\delta\colon G\to\Delta$, $c\colon G\to R^\times$ be homomorphisms and $t\colon G\to R$ any function such that $\rho_Y(g)^2-t(g)\,\rho_Y(g)+c(g)\,D(\delta g)=0$ for all $g$. The conclusion asserts the existence of a commutative ring $k$ that is Artinian and reduced, an algebra over $\mathbb Q$, over $R$ and over $\mathcal O$ with the tower condition, such that $R\to k$ is injective and every nonzero element of $\mathcal O$ maps to a unit of $k$; together with a $k$-module $M$, also an $R$- and $\mathcal O$-module with all compatibilities, finite over $k$ and faithful over $k$ in the same pointwise sense; homomorphisms $\rho_M\colon G\to\mathrm{End}_k(M)$ and $d_M\colon G\to k^\times$ satisfying $\rho_M(g)^2-t(g)\rho_M(g)+d_M(g)\cdot 1=0$ (with $t(g)$ pushed along $R\to k$); and an injective $R$-linear map $\iota\colon Y\to M$ intertwining $\rho_Y$ and $\rho_M$, such that every $m\in M$ admits a nonzero $a\in\mathcal O$ with $a\cdot m$ in the image of $\iota$.
--
--   This is the passage to the generic fibre in Wiles' argument bounding the image of a two-dimensional representation with values in a reduced finite algebra: the coefficient ring is enlarged so as to absorb the central character, becoming a reduced Artinian $\mathbb Q$-algebra over which the module is faithful and finite, and the quadratic relation is replaced by one with scalar constant term. It is used by [`Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced`](thm.html#Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [IsReduced R]
    {G : Type} [Group G]
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    [Module.Finite 𝒪 Y] [Module.IsTorsionFree 𝒪 Y]
    (hfaith : ∀ x : R, (∀ y : Y, x • y = 0) → x = 0)
    (ρY : G →* Module.End R Y)
    {Δ : Type} [CommGroup Δ] [Finite Δ] (D : Δ →* Module.End R Y)
    (hD : ∀ (d : Δ) (g : G), D d * ρY g = ρY g * D d)
    (δ : G →* Δ) (c : G →* Rˣ) (t : G → R)
    (hrel : ∀ g : G, ρY g * ρY g - (t g) • ρY g + ((c g : Rˣ) : R) • D (δ g) = 0) :
    ∃ (k : Type) (_ : CommRing k) (_ : IsArtinianRing k) (_ : IsReduced k) (_ : Algebra ℚ k)
      (_ : Algebra R k) (_ : Algebra 𝒪 k) (_ : IsScalarTower 𝒪 R k)
      (_ : Function.Injective (algebraMap R k))
      (_ : ∀ a : 𝒪, a ≠ 0 → IsUnit (algebraMap 𝒪 k a))
      (M : Type) (_ : AddCommGroup M) (_ : Module k M) (_ : Module R M) (_ : Module 𝒪 M)
      (_ : IsScalarTower R k M) (_ : IsScalarTower 𝒪 k M) (_ : IsScalarTower 𝒪 R M) (_ : Module.Finite k M)
      (_ : ∀ x : k, (∀ m : M, x • m = 0) → x = 0)
      (ρM : G →* Module.End k M) (dM : G →* kˣ)
      (_ : ∀ g : G, ρM g * ρM g - (algebraMap R k (t g)) • ρM g + ((dM g : kˣ) : k) • (1 : Module.End k M) = 0)
      (ι : Y →ₗ[R] M) (_ : Function.Injective ι)
      (_ : ∀ (g : G) (y : Y), ι (ρY g y) = ρM g (ι y)),
      ∀ m : M, ∃ a : 𝒪, a ≠ 0 ∧ a • m ∈ LinearMap.range ι := by sorry
