-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/9b29bc2d-406c-57d5-a333-d8c4bc1f970f
-- title:
--   Quotient of an abelian scheme by a finite flat subgroup
-- statement:
--   Let $R$ be a commutative ring, let $f : J \to \operatorname{Spec} R$ be a morphism of schemes and let $L$ be a relative group law on $f$, i.e. a group structure on the set $\{\varphi : T \to J \mid \varphi \circ f = t\}$ of sections of $f$ over each $t : T \to \operatorname{Spec} R$, natural in $T$ under composition. Assume: $f$ carries the bundle `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ of the underlying map is connected, and $f$ admits some relative group law; $L$ is commutative on all sections; and $\iota : E \to J$ is a closed immersion with $\iota$ followed by $f$ finite, flat and locally of finite presentation, such that the sections of $f$ which factor through $\iota$ contain the identity and are closed under the multiplication and inversion of $L$. Assume further that for every point $x \in J$ there is an affine open $U \subseteq J$ containing the image under the action morphism $L.\mathrm{action}\,\iota$ (the $L$-product of $\mathrm{pr}_1$ followed by $\iota$ with $\mathrm{pr}_2$) of every point of $\mathrm{pullback}(\iota \circ f, f)$ lying over $x$ via $\mathrm{pr}_2$. Then there exist a scheme $P$, a morphism $g : P \to \operatorname{Spec} R$, a relative group law $LP$ on $g$, a morphism $p : J \to P$ with $p$ followed by $g$ equal to $f$, and an identity $w$ equalising $\mathrm{pr}_2$ and the action morphism after $p$, such that: $g$ carries `AbelianSchemePropertyBundle`; $LP$ is commutative; $p$ is finite, flat, locally of finite presentation and surjective; composition with $p$ sends $L$-products of sections to $LP$-products; a section $x$ of $f$ has $x$ followed by $p$ equal to the identity section of $LP$ precisely when $x$ factors through $\iota$; the square formed by $\mathrm{pr}_2$, the action morphism and two copies of $p$ is a pullback; and the cofork of $p$ with respect to $w$ is a colimit.
--
--   This is the construction of the quotient of a commutative abelian scheme by a finite flat closed subgroup scheme as an abelian scheme, with the isogeny $p$ as the quotient map and $E$ as its kernel, here over an arbitrary commutative base ring and under the hypothesis that each orbit of the action groupoid lies in an affine open of $J$. It is used in the construction of quotients of fake elliptic curves by finite flat stable subgroups in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup_of_affineOrbit_of_commRing
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
    [IsFinite (ι ≫ f)] [Flat (ι ≫ f)] [LocallyOfFinitePresentation (ι ≫ f)]
    (hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      ∃ e : T ⟶ E, e ≫ ι = (L.one t).1)
    (hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
        ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1)
    (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)
    (haff : ∀ x : J, ∃ U : J.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (ι ≫ f) f), (pullback.snd (ι ≫ f) f) r = x → (L.action ι) r ∈ U) :
    ∃ (P : Scheme.{u}) (g : P ⟶ Spec (CommRingCat.of R)) (LP : RelativeGroupLaw R g)
      (p : J ⟶ P) (hg : p ≫ g = f) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p),
      AbelianSchemePropertyBundle R g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        LP.mul t x y = LP.mul t y x) ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ : SchemeHomOver t g) = LP.one t ↔
          ∃ e : T ⟶ E, e ≫ ι = x.1) ∧
      IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p ∧
      Nonempty (IsColimit (Cofork.ofπ p w)) := by sorry
