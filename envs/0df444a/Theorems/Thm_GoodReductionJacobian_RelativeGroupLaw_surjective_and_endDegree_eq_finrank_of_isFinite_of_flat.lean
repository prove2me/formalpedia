-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
-- name    : GoodReductionJacobian.RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/7a59b509-9bc2-53dd-8db6-ea031b8f023a
-- title:
--   Finite flat endomorphisms: surjectivity and degree equals kernel order
-- statement:
--   Let $K$ be a field, $A$ a scheme and $f \colon A \to \operatorname{Spec} K$ a morphism that is locally of finite type, with $A$ preconnected as a topological space. Let $L$ be a `RelativeGroupLaw` for $f$: a multiplication, unit and inversion on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, natural in $T$, for all $K$-schemes $t \colon T \to \operatorname{Spec} K$, satisfying associativity, the two unit laws, left inversion, and naturality of the multiplication along $K$-morphisms $T' \to T$. Let $\beta$ be an element of `SchemeHomOver f f`, i.e. a morphism $\beta \colon A \to A$ with $\beta$ followed by $f$ equal to $f$, and assume that $\beta$ is a finite and flat morphism of schemes. The conclusion is threefold: the underlying map of $\beta$ on points is surjective; the natural number $L.\mathrm{endDegree}\,\beta$ is positive; and for every point $x$ of $A$ one has $L.\mathrm{endDegree}\,\beta = \mathrm{finrank}\,\beta\,x$. Here $\mathrm{endDegree}$ is defined as the $\mathrm{finrank}$, at the closed point of $\operatorname{Spec} K$, of the projection to $\operatorname{Spec} K$ of the fibre product of $\beta$ with the unit section $L.\mathrm{one}$ over the identity of $\operatorname{Spec} K$, when that projection is finite, and as $0$ otherwise.
--
--   This is the identification "degree of an isogeny equals the order of its kernel", here for an arbitrary finite flat endomorphism of a connected scheme over a field carrying a group law on its functor of points, together with surjectivity of such an endomorphism. It is used in the treatment of Jacobians with good reduction and of the quaternionic fake elliptic curves, for instance in establishing surjectivity of endomorphisms built from Frobenius and from multiplication by $n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧
      ∀ x : A, L.endDegree β = Scheme.Hom.finrank β.1 x := by sorry
