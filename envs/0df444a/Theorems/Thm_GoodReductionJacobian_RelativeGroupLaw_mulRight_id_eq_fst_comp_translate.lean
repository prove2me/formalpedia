-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mulRight_id_eq_fst_comp_translate
-- name    : GoodReductionJacobian.RelativeGroupLaw.mulRight_id_eq_fst_comp_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ecbfee8e-b10b-5b85-82f0-6ade418f62a8
-- title:
--   Right multiplication over the identity base equals pr₁ followed by translation
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} R$ be a morphism. Let $L$ be a relative group law on $f$ in the sense of the structure `RelativeGroupLaw`: for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ it supplies a group structure (multiplication, unit, inverse, with associativity, the two unit laws and left inverses) on the set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over $t$, these multiplications being natural for base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $x$ be a point of $A$ over the identity of $\operatorname{Spec} R$, i.e. a morphism $x : \operatorname{Spec} R \to A$ with $x$ followed by $f$ the identity. The assertion is the equality of morphisms $\operatorname{pullback} f\,(\mathbf 1_{\operatorname{Spec} R}) \to A$ between, on the one hand, `L.mulRight` at the test object $t = \mathbf 1_{\operatorname{Spec} R}$ and the point $x$, namely the underlying morphism of the $L$-product, taken over $\mathrm{pr}_2$ followed by $\mathbf 1$, of the point $\mathrm{pr}_1$ (a point over that structure morphism by the pullback condition) with the point $\mathrm{pr}_2$ followed by $x$, and, on the other hand, $\mathrm{pr}_1$ followed by `L.translate x`, where the latter is the underlying morphism of the $L$-product over $f$ of the identity point $\mathbf 1_A$ with the point $f$ followed by $x$.
--
--   This is one of the dictionary lemmas relating the two descriptions of translation by a section in a relative group law: the universal right-multiplication morphism on a base change and the endomorphism $T_x$ of $A$ itself. It is used in the analysis of stabilisers of polarisations, where an identity of morphisms out of $A$ involving $T_x$ has to be converted into a statement about the relative group law over a test scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_mulRight_id_eq_fst_comp_translate.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.mulRight_id_eq_fst_comp_translate
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.mulRight (𝟙 (Spec (CommRingCat.of R))) x = pullback.fst f (𝟙 (Spec (CommRingCat.of R))) ≫ L.translate x := by sorry
