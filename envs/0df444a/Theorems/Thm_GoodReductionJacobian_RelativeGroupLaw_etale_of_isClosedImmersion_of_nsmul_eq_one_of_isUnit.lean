-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_of_isClosedImmersion_of_nsmul_eq_one_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.etale_of_isClosedImmersion_of_nsmul_eq_one_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/82d82534-a98d-5430-83d5-beaf5eb99032
-- title:
--   Closed n-torsion subschemes are étale when n is invertible
-- statement:
--   Let $R$ be a commutative ring and let $f : A \to \operatorname{Spec} R$ be a scheme over $R$ equipped with a `RelativeGroupLaw` $G$: functorially in a scheme $T$ over $R$ with structure morphism $t$, a group structure (multiplication, unit, inverse, with associativity, unit laws, left inverse law) on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, the multiplication being compatible with base change along morphisms $T' \to T$ over $R$. Assume the multiplication is commutative on all such point sets ($hcomm$). Let $n$ be a natural number whose image in $R$ is a unit, and let $i : X \to A$ be a closed immersion such that the composite $X \to A \to \operatorname{Spec} R$ is flat and locally of finite presentation, and such that the tautological $X$-point $i$ of $A$ over $i \circ f$ is killed by $n$, i.e. the $n$-fold iterate of the group law applied to it (defined by recursion, $0$ giving the unit) equals the unit point ($htors$). The conclusion has two parts: first, $X \to \operatorname{Spec} R$ is étale; second, for every scheme $P$ and every morphism $p : A \to P$ that is flat, surjective and quasi-compact and for which the square formed by the second projection $X \times_{\operatorname{Spec} R} A \to A$ of the pullback of $i \circ f$ along $f$, the action morphism $G.action\ i$ sending $(x,a)$ to $i(x)\cdot a$, and $p$ on both remaining sides is cartesian, the morphism $p$ is étale.
--
--   This is the statement that a closed flat, locally finitely presented subgroup-type subscheme killed by an integer invertible on the base is étale over the base, together with the statement that a flat, surjective, quasi-compact map whose kernel pair is the translation action of such a subscheme is an étale isogeny. It is used in the construction of level structures and isogenies for fake elliptic curves and in the study of kernels of relative group laws on Weierstrass models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_etale_of_isClosedImmersion_of_nsmul_eq_one_of_isUnit.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.etale_of_isClosedImmersion_of_nsmul_eq_one_of_isUnit
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    {X : Scheme.{u}} (i : X ⟶ A) [IsClosedImmersion i] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    (htors : G.nsmul (i ≫ f) n ⟨i, rfl⟩ = G.one (i ≫ f)) :
    Etale (i ≫ f) ∧
    ∀ {P : Scheme.{u}} (p : A ⟶ P), Flat p → Surjective p → QuasiCompact p →
      IsPullback (pullback.snd (i ≫ f) f) (G.action i) p p → Etale p := by sorry
