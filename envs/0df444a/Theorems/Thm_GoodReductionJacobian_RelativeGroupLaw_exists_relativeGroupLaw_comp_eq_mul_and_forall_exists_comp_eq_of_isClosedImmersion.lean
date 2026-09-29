-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/6dbb7bcf-279a-5be9-89f9-cc8e2158c721
-- title:
--   Closed subfunctor inherits a relative group law; endomorphisms restrict
-- statement:
--   Let $R$ be a commutative ring, let $f : J \to \operatorname{Spec} R$ be a scheme over $R$, and let $L$ be a `RelativeGroupLaw` for $f$: an assignment, to every scheme $T$ and every $t : T \to \operatorname{Spec} R$, of a multiplication, a unit and an inversion on the set of morphisms $T \to J$ over $t$, satisfying associativity, the unit laws, left inversion, and naturality under base morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$; assume $L$ is commutative, i.e. its multiplication is commutative on every such set. Let $a : \mathcal{A} \to \operatorname{Spec} R$ be a further scheme over $R$ and $\iota : \mathcal{A} \to J$ a morphism with $\iota \circ$ (i.e. followed by) $f$ equal to $a$, whose underlying morphism of schemes is a closed immersion. Assume that for every $T$ and every $s : T \to \operatorname{Spec} R$ the image of $\iota$ on $s$-points is closed under the group operations in the strong sense: the unit $L.\mathrm{one}\,s$ factors through $\iota$; for all $s$-points $x,y$ of $\mathcal{A}$ there is an $s$-point $z$ of $\mathcal{A}$ with $\iota \circ z = L.\mathrm{mul}\,s\,(\iota\circ x)\,(\iota\circ y)$; and for every $x$ there is $z$ with $\iota\circ z = L.\mathrm{inv}\,s\,(\iota\circ x)$. The conclusion asserts the existence of a commutative relative group law $L_{\mathcal{A}}$ for $a$ such that $\iota \circ (L_{\mathcal{A}}.\mathrm{mul}\,s\,x\,y) = L.\mathrm{mul}\,s\,(\iota\circ x)\,(\iota\circ y)$ for all $T$, $s$ and all $s$-points $x,y$ of $\mathcal{A}$ (compatibility of $\iota$ with the unit and the inversion is not recorded), together with: for every endomorphism $E$ of $J$ over $\operatorname{Spec} R$ which is multiplicative for $L$ on all point sets and which maps the $\iota$-image into itself (for all $T$, $s$ and $s$-points $x$ of $\mathcal{A}$ there is an $s$-point $z$ of $\mathcal{A}$ with $\iota\circ z = E \circ \iota \circ x$), there exists an endomorphism $E'$ of $\mathcal{A}$ over $\operatorname{Spec} R$ that is multiplicative for $L_{\mathcal{A}}$ on all point sets and satisfies $\iota \circ E' = E \circ \iota$.
--
--   This is the functorial form of the statement that a closed subscheme of a commutative group scheme whose points are stable under unit, multiplication and inversion is itself a group scheme, and that endomorphisms preserving the subscheme restrict to it as homomorphisms; here group schemes are handled through group laws on point sets natural in the base, rather than through multiplication morphisms. It is used in the construction of level structures on fake elliptic curves in the Čerednik–Drinfeld setting, and in the analysis of $p$-divisible groups attached to points of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_and_forall_exists_comp_eq_of_isClosedImmersion
    {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : GoodReductionJacobian.RelativeGroupLaw R f) (hc : L.IsCommutative)
    {𝒜 : Scheme.{0}} (a : 𝒜 ⟶ Spec (CommRingCat.of R)) (ι : SchemeHomOver a f) [IsClosedImmersion ι.1]
    (hgrp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)),
      (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι = L.one s) ∧
      (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
      (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
        L.inv s (NeronModelInfra.schemeHomOverComp x ι))) :
    ∃ L𝒜 : GoodReductionJacobian.RelativeGroupLaw R a, L𝒜.IsCommutative ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a),
        NeronModelInfra.schemeHomOverComp (L𝒜.mul s x y) ι =
          L.mul s (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
      ∀ E : SchemeHomOver f f,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) E = L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s a),
          ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) E) →
        ∃ E' : SchemeHomOver a a,
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s a),
            NeronModelInfra.schemeHomOverComp (L𝒜.mul s x y) E' = L𝒜.mul s (NeronModelInfra.schemeHomOverComp x E') (NeronModelInfra.schemeHomOverComp y E')) ∧
          E'.1 ≫ ι.1 = ι.1 ≫ E.1 := by sorry
