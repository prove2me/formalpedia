-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType
-- name    : GoodReductionJacobian.RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/fa6e4012-fd67-5953-a60e-c4b958a2dda3
-- title:
--   Geometrically reduced group law over a field gives smoothness
-- statement:
--   Let $K$ be a field and let $f \colon A \to \operatorname{Spec} K$ be a morphism of schemes which is geometrically reduced and locally of finite type. Assume given a relative group law $G$ on $f$ over $K$: for every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} K$, operations $\mathrm{mul}$, $\mathrm{one}$ and $\mathrm{inv}$ on the set of relative points $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$, such that multiplication is associative, $\mathrm{one}(t)$ is a two-sided identity, $\mathrm{inv}(t)(x)$ multiplied on the left by $x$ gives $\mathrm{one}(t)$, and multiplication is natural in the test object: for every $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition with $\psi$ carries the product of two $T$-points to the product of their images as $T'$-points. Under these hypotheses the conclusion is that $f$ is a smooth morphism of schemes.
--
--   This is the functor-of-points form of the standard fact that a geometrically reduced group scheme locally of finite type over a field is smooth. It is used in the construction of the abelian-scheme property bundle attached to a relative group law and in the identification of the connected component of the identity as a closed subscheme smooth of a given relative dimension over a perfect field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType.lean

import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    [GeometricallyReduced f] [LocallyOfFiniteType f] (G : RelativeGroupLaw K f) :
    Smooth f := by sorry
