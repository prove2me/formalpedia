-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul
-- name    : GoodReductionJacobian.RelativeGroupLaw.comp_translate_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/26dc9aa2-d77e-5a69-8261-8c511540326e
-- title:
--   Translation composed with a point is multiplication by the constant point
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} R$ be a morphism, and let $L$ be a relative group law on $f$: that is, a family of binary operations `mul`, a distinguished element `one` and an operation `inv` on each set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of morphisms over a morphism $t : T \to \operatorname{Spec} R$, satisfying associativity, the two unit laws, left inversion, and naturality of `mul` under precomposition with a morphism $\psi : T' \to T$ satisfying $\psi$ followed by $t$ equal to $t'$. Let $t : T \to \operatorname{Spec} R$ be a further scheme over $\operatorname{Spec} R$, let $z$ be a morphism $T \to A$ with $z$ followed by $f$ equal to $t$, and let $x$ be a morphism $\operatorname{Spec} R \to A$ with $x$ followed by $f$ equal to the identity of $\operatorname{Spec} R$. Recall that `RelativeGroupLaw.translate` assigns to $x$ the endomorphism of $A$ underlying the product, taken over the structure morphism $f$ itself, of the point $\mathrm{id}_A$ with the point $f$ followed by $x$. The conclusion is the equality of morphisms $T \to A$ given by $z$ followed by $L.\mathrm{translate}\,x$ and the morphism underlying the product, over $t$, of $z$ with the point `schemeHomOverComp t (Category.comp_id t) x`, whose underlying morphism is $t$ followed by $x$.
--
--   This is the dictionary between the geometric translation map $T_x : A \to A$ attached to an $R$-point $x$ of a group scheme and the group operation on points: composing a $T$-point $z$ with $T_x$ gives the product of $z$ with the base change of $x$ along $t$. It is used in the study of polarisations and abelian-scheme property bundles, where translations must be converted into products of points over a varying test scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.comp_translate_eq_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    z.1 ≫ L.translate x = (L.mul t z (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x)).1 := by sorry
