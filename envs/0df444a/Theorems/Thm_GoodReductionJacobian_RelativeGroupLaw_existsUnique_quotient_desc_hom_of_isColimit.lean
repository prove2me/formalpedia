-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/802ff930-ea80-5d94-9022-76269e82afb3
-- title:
--   Homomorphisms killing E factor uniquely through the quotient
-- statement:
--   Let $R$ be a commutative ring, $f \colon J \to \operatorname{Spec} R$ a morphism of schemes and $L$ a relative group law on $f$, i.e. a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws and compatibility with base change along morphisms $T' \to T$ over $\operatorname{Spec} R$) on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to J$ over a given $t \colon T \to \operatorname{Spec} R$. Let $\iota \colon E \to J$ be a morphism, and let $p \colon J \to P$ be a flat surjective morphism satisfying $\mathrm{pr}_2 \circ p = L.\mathrm{action}\,\iota$ followed by $p$ on $E \times_{\operatorname{Spec} R} J =$ `pullback (ι ≫ f) f`, where the action sends a point $(e,x)$ to the $L$-product of $\iota(e)$ and $x$; assume the resulting cofork exhibits $p$ as the coequaliser of these two morphisms. Let $g \colon P \to \operatorname{Spec} R$ with $p$ followed by $g$ equal to $f$, and let $LP$ be a relative group law on $g$ for which $p$ is a homomorphism: composing an $L$-product of two $T$-points of $J$ with $p$ gives the $LP$-product of their composites with $p$. Let $gX \colon X \to \operatorname{Spec} R$ carry a relative group law $LX$, and let $\varphi \colon J \to X$ satisfy $\varphi$ followed by $gX$ equal to $f$, be a homomorphism from $L$ to $LX$ in the same sense, and kill $E$, in that for every $T$ and every $e \colon T \to E$ with $e \circ \iota \circ f = t$ the $T$-point $(e \circ \iota)$ followed by $\varphi$ is the $LX$-unit of $t$. Then there is a unique morphism $\psi \colon P \to X$ with $\psi$ followed by $gX$ equal to $g$ such that $p$ followed by $\psi$ is $\varphi$ and $\psi$ is a homomorphism from $LP$ to $LX$.
--
--   This is the universal property of the quotient of a relative group scheme by the action of a subscheme $E$, formulated for relative group laws on the functor of points: homomorphisms out of $J$ that are trivial on $E$ factor uniquely through $J \to J/E$, and the factorisation is again a homomorphism. It is used in the construction of quotients of fake elliptic curves by stable finite flat subgroup schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {E : Scheme.{u}} (ι : E ⟶ J)
    {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
    [Flat p] [Surjective p]
    (hcoeq : IsColimit (Cofork.ofπ p w))
    {g : P ⟶ Spec (CommRingCat.of R)} (hg : p ≫ g = f) (LP : RelativeGroupLaw R g)
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
        LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩)
    {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} (LX : RelativeGroupLaw R gX)
    (φ : SchemeHomOver f gX)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(L.mul t x y).1 ≫ φ.1, by rw [Category.assoc, φ.2, (L.mul t x y).2]⟩ : SchemeHomOver t gX) =
        LX.mul t ⟨x.1 ≫ φ.1, by rw [Category.assoc, φ.2, x.2]⟩ ⟨y.1 ≫ φ.1, by rw [Category.assoc, φ.2, y.2]⟩)
    (hφE : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (he : e ≫ ι ≫ f = t),
      (⟨(e ≫ ι) ≫ φ.1, by simp only [Category.assoc, φ.2, he]⟩ : SchemeHomOver t gX) = LX.one t) :
    ∃! ψ : SchemeHomOver g gX, p ≫ ψ.1 = φ.1 ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t g),
        (⟨(LP.mul t u v).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (LP.mul t u v).2]⟩ : SchemeHomOver t gX) =
          LX.mul t ⟨u.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, u.2]⟩ ⟨v.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, v.2]⟩ := by sorry
