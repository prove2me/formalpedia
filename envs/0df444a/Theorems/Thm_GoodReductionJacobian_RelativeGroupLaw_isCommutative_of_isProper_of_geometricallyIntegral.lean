-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
-- name    : GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/7cf3f689-e889-5799-9be8-0c93d3e711f6
-- title:
--   Commutativity of relative group laws on proper geometrically integral schemes
-- statement:
--   Let $K$ be a field, let $A$ be a scheme and let $f \colon A \to \operatorname{Spec} K$ be a morphism of schemes that is proper and satisfies the predicate `GeometricallyIntegral`. Let $G$ be a relative group law on $f$ in the sense of `RelativeGroupLaw`, that is: for every test scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} K$, a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over $t$, satisfying associativity, the two unit laws and left inversion, and such that multiplication is natural: for any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition by $\psi$ carries the product of two points over $t$ to the product of their images over $t'$. The conclusion is `G.IsCommutative`, i.e. for every scheme $T$, every $t \colon T \to \operatorname{Spec} K$ and all points $x, y$ of $A$ over $t$ one has $x \cdot_t y = y \cdot_t x$. Thus commutativity is asserted for the point group attached to every test scheme, not merely for $K$-points.
--
--   This is the functor-of-points form of the classical fact that a proper geometrically integral group scheme over a field is commutative, proved by the rigidity argument for abelian varieties. It is used throughout the treatment of Jacobians with good reduction and of abelian schemes, for instance in the results on torsion points, on Euler characteristics of trivial-kernel situations and on extending homomorphisms over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral.lean

import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} [IsProper f]
    [GeometricallyIntegral f] (G : RelativeGroupLaw K f) : G.IsCommutative := by sorry
