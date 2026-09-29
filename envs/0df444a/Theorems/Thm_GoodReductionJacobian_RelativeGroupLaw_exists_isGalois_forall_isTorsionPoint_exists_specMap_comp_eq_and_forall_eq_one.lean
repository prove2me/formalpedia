-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/732a3b48-0573-516f-aa95-978989778204
-- title:
--   The n-division field is finite Galois with faithful action
-- statement:
--   Let $K$ be a field and let $f\colon A\to\operatorname{Spec}K$ be a morphism of schemes, equipped with a relative group law $G$ in the sense of `RelativeGroupLaw`: for every scheme $T$ and every $K$-structure morphism $t\colon T\to\operatorname{Spec}K$ a multiplication, unit and inversion on the set $\{\varphi\colon T\to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over $t$, satisfying the group axioms and compatible with base change along any $\psi\colon T'\to T$ over $\operatorname{Spec}K$. Assume these group laws are commutative (`hcomm`), that `hA` holds, i.e. $f$ is smooth and proper, each fibre of the underlying map of $f$ over a point of $\operatorname{Spec}K$ is connected, and $A$ admits some relative group law over $K$, and that $f$ is smooth of relative dimension $d$. Let $n$ be a natural number with $(n:K)\neq 0$, and let $\Omega$ be a field extension of $K$ that is normal over $K$. Then there is an intermediate field $L$ with $K\subseteq L\subseteq\Omega$ such that $L$ is finite-dimensional and Galois over $K$ and: (1) for every $\Omega$-point $x$ of $A$ over $K$ with $G$-torsion of order $n$, i.e. the $n$-fold product $((1\cdot x)\cdots x)$ formed from the unit equals the unit, there is an $L$-point $z$ of $A$ over $K$, again $n$-torsion for $G$, with $\operatorname{Spec}(\Omega)\to\operatorname{Spec}(L)$ followed by $z$ equal to $x$; and (2) any $K$-algebra automorphism $\tau$ of $L$ fixing every $n$-torsion $L$-point $z$, in the sense that $\operatorname{Spec}(\tau)$ followed by $z$ equals $z$, is the identity.
--
--   This is the opening step of the Serre–Tate treatment of the criterion of Néron–Ogg–Shafarevich: the $n$-torsion of an abelian variety $A/K$ becomes rational over a finite Galois extension $L=K(A[n])$ of $K$ inside any normal extension $\Omega$, and $\operatorname{Gal}(L/K)$ acts faithfully on $A[n]$. It is used in the reduction of the good-reduction criterion to a statement about ramification in the finite extension $K(A[n])$, where injectivity of reduction on torsion is available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
    (K : Type u) [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (hA : AbelianSchemePropertyBundle K f) (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      (∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f,
        G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z ∧
          Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ z.1 = x.1) ∧
      (∀ τ : L ≃ₐ[K] L,
        (∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z →
          Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ z.1 = z.1) → τ = 1) := by sorry
