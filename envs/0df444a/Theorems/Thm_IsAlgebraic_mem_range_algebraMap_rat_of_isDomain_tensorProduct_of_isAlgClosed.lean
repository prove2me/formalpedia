-- Prove2me | Theorems.Thm_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
-- name    : IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/406e894c-c6cb-5d42-9a3d-23fb5c4c99eb
-- title:
--   Algebraic elements are rational when K⊗_ℚC is a domain
-- statement:
--   Let $K$ be a field of characteristic zero and let $C$ be an algebraically closed field of characteristic zero. Assume that the $\mathbb Q$-algebra $K\otimes_{\mathbb Q}C$ is an integral domain (a nontrivial commutative ring without zero divisors). Then for every $x\in K$ that is algebraic over $\mathbb Q$, the element $x$ lies in the range of the structure map $\mathbb Q\to K$, i.e. $x\in\mathrm{Set.range}\,(\mathrm{algebraMap}\ \mathbb Q\ K)$; equivalently $x$ is the image of a rational number. Here $K$ and $C$ are taken in the smallest universe, and the tensor product is formed over $\mathbb Q$ with its canonical algebra structures on both factors. Thus the hypothesis that one algebraically closed field $C$ of characteristic zero has $K\otimes_{\mathbb Q}C$ a domain forces $\mathbb Q$ to be algebraically closed inside $K$.
--
--   This is the statement that $\mathbb Q$ is algebraically closed in $K$ (the field of constants of $K$ over $\mathbb Q$ is $\mathbb Q$) whenever $K\otimes_{\mathbb Q}C$ is a domain for some algebraically closed $C$ of characteristic zero, the algebraic half of the usual criterion for a regular, or geometrically integral, field extension. It is used by [`AlgebraicGeometry.functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback`](thm.html#AlgebraicGeometry.functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback) to identify the constants in a function field from integrality of a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
    (K : Type) [Field K] [CharZero K]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (h : IsDomain (K ⊗[ℚ] C))
    (x : K) (hx : IsAlgebraic ℚ x) :
    x ∈ Set.range (algebraMap ℚ K) := by sorry
