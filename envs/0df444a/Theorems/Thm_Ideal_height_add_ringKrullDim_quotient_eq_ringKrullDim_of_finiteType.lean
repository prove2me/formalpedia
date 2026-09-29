-- Prove2me | Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
-- name    : Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/6ca2b072-c3a0-5fab-989f-23bc23e465df
-- title:
--   Dimension formula for affine domains
-- statement:
--   Let $k$ be a field and let $A$ be an integral domain carrying a $k$-algebra structure which makes it of finite type over $k$, i.e. generated as a $k$-algebra by finitely many elements. Let $P \subseteq A$ be a prime ideal. The assertion is the equality
--   $$\operatorname{ht}(P) + \dim (A/P) = \dim A$$
--   in $\mathrm{WithBot}\ \mathbb{N}_\infty$, where $\operatorname{ht}(P)$ is `Ideal.height`, the supremum of the lengths of chains of primes descending from $P$ (an element of $\mathbb{N}_\infty$, coerced into $\mathrm{WithBot}\ \mathbb{N}_\infty$), and $\dim$ is `ringKrullDim`, the Krull dimension of a commutative ring as an element of $\mathrm{WithBot}\ \mathbb{N}_\infty$, taken for the quotient domain $A/P$ and for $A$ itself. Note that the addition and the equality take place in $\mathrm{WithBot}\ \mathbb{N}_\infty$; since $A$ is a domain and $P$ is prime, both rings occurring are nonzero, so neither dimension is $\bot$. No finiteness of $\dim A$ is hypothesised, and $k$ is arbitrary (no algebraic closedness or perfection).
--
--   This is the classical dimension formula for affine domains over a field: finitely generated domains over a field are equidimensional and catenary, so that the codimension of the irreducible closed subset $V(P)$ of $\operatorname{Spec} A$ plus its dimension equals $\dim \operatorname{Spec} A$. It is the commutative-algebra input to the dimension-theoretic estimates used for schemes over a field in this development, for instance in bounding topological Krull dimension of smooth morphisms of given relative dimension and in the dimension comparisons accompanying integral and finite morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) = ringKrullDim A := by sorry
