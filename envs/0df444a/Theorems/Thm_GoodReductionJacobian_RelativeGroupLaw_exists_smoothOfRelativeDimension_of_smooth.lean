-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/fd606cef-137b-5314-b657-52a857224bcc
-- title:
--   Group law forces constant relative dimension
-- statement:
--   Let $K$ be a field and let $g\colon X \to \operatorname{Spec} K$ be a smooth morphism of schemes (all in a fixed universe). Assume given a relative group law $L$ for $g$ over $K$, that is: for every scheme $T$ and every morphism $t\colon T \to \operatorname{Spec} K$, a multiplication, a distinguished element and an inversion on the set $\{\varphi\colon T \to X \mid \varphi \circ g = t\}$ of $T$-points of $X$ over $t$, subject to associativity, the two unit laws, left inverses, and the naturality requirement that for any $\psi\colon T' \to T$ with $t \circ \psi = t'$ precomposition with $\psi$ carries the multiplication on $T$-points over $t$ to the multiplication on $T'$-points over $t'$. (Only the multiplication is required to be natural; nothing is assumed about compatibility of the units or inverses with base change, and no scheme-theoretic group structure on $X$ itself is posited.) The conclusion is that there exists a natural number $d$ such that $g$ is smooth of relative dimension $d$, i.e. the relative dimension is globally constant, equal to $d$, on all of $X$.
--
--   This is the equidimensionality of a smooth group scheme over a field: a smooth morphism to a field whose functor of points carries a group law has one and the same relative dimension everywhere. It is used in the treatment of polarisations and of Néron models, where statements about abelian schemes and Jacobians require a single numerical relative dimension rather than a locally constant one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth
    {K : Type u} [Field K] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of K)} [Smooth g]
    (L : RelativeGroupLaw K g) :
    ∃ d : ℕ, SmoothOfRelativeDimension d g := by sorry
