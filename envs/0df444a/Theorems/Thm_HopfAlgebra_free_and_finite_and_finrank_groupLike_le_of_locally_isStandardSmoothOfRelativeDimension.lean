-- Prove2me | Theorems.Thm_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
-- name    : HopfAlgebra.free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/28c9ecf6-c1ca-5ba3-84bd-9be82600c003
-- title:
--   Group-like elements of a connected smooth Hopf algebra
-- statement:
--   Let $k$ be a field and let $H$ be a commutative ring carrying the structure of a Hopf algebra over $k$ (both in the same universe), such that the prime spectrum $\operatorname{Spec} H$ is a connected topological space. Let $h$ be a natural number and assume that the structure map $k \to H$ is locally standard smooth of relative dimension $h$ in the sense of `RingHom.Locally`: there is a family of elements of $H$ generating the unit ideal such that each of the induced maps from $k$ to the corresponding localisation of $H$ is standard smooth of relative dimension $h$, i.e. admits a presentation by finitely many polynomial variables and relations whose Jacobian is invertible, with the number of variables minus the number of relations equal to $h$. The conclusion is a threefold conjunction about the group $\mathrm{GroupLike}\ k\ H$ of group-like elements of $H$, written additively and hence regarded as a $\mathbb{Z}$-module: it is free over $\mathbb{Z}$, it is finite (finitely generated) over $\mathbb{Z}$, and its $\mathbb{Z}$-rank is at most $h$.
--
--   In geometric language, $G = \operatorname{Spec} H$ is a connected affine group scheme over $k$ which is smooth of relative dimension $h$, and the group-like elements of $H$ are the characters $G \to \mathbb{G}_m$; the statement is the classical fact that the character group of a connected smooth affine algebraic group is free abelian of rank at most the dimension, with equality for tori. It is used, via the bound on the number of torsion points, in [`GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine`](thm.html#GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem HopfAlgebra.free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
    (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
    [ConnectedSpace (PrimeSpectrum H)] (h : ℕ)
    (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H)) :
    Module.Free ℤ (Additive (GroupLike k H)) ∧ Module.Finite ℤ (Additive (GroupLike k H)) ∧
      Module.finrank ℤ (Additive (GroupLike k H)) ≤ h := by sorry
