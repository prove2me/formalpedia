-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_mul_fst
-- name    : GoodReductionJacobian.RelativeGroupLaw.isPullback_mul_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/98b49c9d-f250-5a71-b98c-0dcaa0fdaac4
-- title:
--   Multiplication and first projection form a cartesian square
-- statement:
--   Let $R$ be a commutative ring, $G$ a scheme and $g \colon G \to \operatorname{Spec} R$ a morphism, and let `LG` be a relative group law on $g$ in the sense of `RelativeGroupLaw`: for every test scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to G \mid \varphi \text{ followed by } g = t\}$ of $T$-points of $G$ over $t$, subject to associativity, both unit laws, the left inverse law, and naturality of the multiplication under precomposition with any $\psi \colon T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$. Take as test object the fibre product $G \times_{\operatorname{Spec} R} G$ with structure morphism $p_1$ followed by $g$, and let $m$ be the underlying morphism $G \times_{\operatorname{Spec} R} G \to G$ of the product of the two points $p_1$ and $p_2$ (the latter viewed over $p_1$ followed by $g$ using the pullback condition). The conclusion is that the square with edges $m$, $p_1$ on top and left and $g$, $g$ on bottom and right is a pullback square: $m$ followed by $g$ equals $p_1$ followed by $g$, and $(m, p_1)$ exhibits $G \times_{\operatorname{Spec} R} G$ as a fibre product of $g$ with itself.
--
--   This is the statement that the universal left translation, or shear, $(a, y) \mapsto (a, a \cdot y)$ of a relative group scheme is an automorphism of $G \times_{\operatorname{Spec} R} G$, in the form that the multiplication together with the first projection realises the fibre product. It is used in the study of top-degree relative differential forms on a group scheme, where it lets one identify the pullback along the multiplication with the pullback along a projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_mul_fst.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isPullback_mul_fst
    {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)} (LG : RelativeGroupLaw R g) :
    IsPullback
      (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).1
      (pullback.fst g g) g g := by sorry
