-- Prove2me | Theorems.Thm_LinearMap_finrank_ker_dualMap_eq_finrank_ker
-- name    : LinearMap.finrank_ker_dualMap_eq_finrank_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/119ce0cf-b22c-530b-acac-0c426ecee163
-- title:
--   Kernel of the dual map has the same dimension
-- statement:
--   Let $K$ be a field and $V$ a finite-dimensional $K$-vector space, and let $f \colon V \to V$ be a $K$-linear endomorphism. Write $f^\vee \colon V^\vee \to V^\vee$ for the dual (transpose) map on $V^\vee = \mathrm{Hom}_K(V,K)$, sending $\lambda$ to $\lambda \circ f$. The assertion is the equality of finite ranks $$\operatorname{finrank}_K \ker(f^\vee) = \operatorname{finrank}_K \ker(f),$$ i.e. the kernel of the transpose, a subspace of the dual space $V^\vee$, has the same dimension over $K$ as the kernel of $f$ itself. The statement is restricted to endomorphisms (same source and target), which is what makes the two kernels live in spaces of equal dimension; Mathlib's corresponding result for ranges, valid for maps between possibly different finite-dimensional spaces, is the companion fact that $f$ and $f^\vee$ have equal rank.
--
--   This is the dual-space form of the classical statement that a square matrix and its transpose have the same nullity (equivalently, row rank equals column rank). It is used to compare eigenspaces of an operator on a representation with those of the contragredient representation on the dual, and is cited by [`groupCohomology.finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul`](thm.html#groupCohomology.finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_finrank_ker_dualMap_eq_finrank_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Module

theorem LinearMap.finrank_ker_dualMap_eq_finrank_ker
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by sorry
