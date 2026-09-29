-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_idempotent
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_idempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/95e8957e-254a-5f61-a980-6585ab5a841f
-- title:
--   Image of an idempotent endomorphism of a commutative relative group law
-- statement:
--   Let $R$ be a commutative ring and $g\colon A \to \operatorname{Spec} R$ a morphism of schemes, and let $L$ be a `RelativeGroupLaw` for $g$: a group structure $\mathrm{mul}\,t$, $\mathrm{one}\,t$, $\mathrm{inv}\,t$ on the set of $\varphi \colon T \to A$ with $\varphi \circ g = t$, for every $t \colon T \to \operatorname{Spec} R$, satisfying associativity, the unit and inverse laws, and compatibility with precomposition by any $\psi \colon T' \to T$ over $\operatorname{Spec} R$. Assume $L$ is commutative on all such point sets, and that $g$ is separated, affine, flat and locally of finite type. Let $e$ be an endomorphism of $A$ with $e \circ g = g$ such that composing points with $e$ is a homomorphism for $L$ on every point set, and such that $e$ is idempotent, $e \circ e = e$. Then there are a scheme $E$, a morphism $i \colon E \to A$ and a relative group law $L_E$ for $i \circ g$ such that $i$ is a closed immersion, $i \circ g$ is affine, flat and locally of finite type, $L_E$ is commutative, composition with $i$ carries $L_E$-products to $L$-products, and for every $t \colon T \to \operatorname{Spec} R$ a point $x$ of $A$ over $t$ satisfies $e \circ x = x$ if and only if $x = i \circ y$ for some point $y$ of $E$ over $t$.
--
--   This is the construction of the image $eA$ of an idempotent endomorphism of a commutative group scheme as a closed subgroup scheme, here in the language of relative group laws on functors of points, together with the inheritance of affineness, flatness and local finite type. It is used in the construction of the $\mathfrak{P}$-primary part of torsion on the Néron model of $J_0(N)$, where applying it to the complementary idempotent yields kernels as well as images.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_idempotent.lean

import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_idempotent
    {R : Type u} [CommRing R] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    [IsSeparated g] [IsAffineHom g] [Flat g] [LocallyOfFiniteType g]
    (e : SchemeHomOver g g)
    (he_hom : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) e =
        L.mul s (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e))
    (he_idem : e.1 ≫ e.1 = e.1) :
    ∃ (E : Scheme.{u}) (i : E ⟶ A) (LE : RelativeGroupLaw R (i ≫ g)),
      IsClosedImmersion i ∧ IsAffineHom (i ≫ g) ∧ Flat (i ≫ g) ∧ LocallyOfFiniteType (i ≫ g) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ g)),
        LE.mul t x y = LE.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ g)),
        NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp x e = x ↔
          ∃ y : SchemeHomOver t (i ≫ g), NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩ = x) := by sorry
