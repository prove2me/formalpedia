-- Prove2me | Theorems.Thm_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
-- name    : IsLocalRing.exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/248920bd-f524-5908-90db-6f153fc13cb5
-- title:
--   Coheight-one prime avoiding a given non-zero element
-- statement:
--   Let $R$ be a commutative ring in a fixed universe which is an integral domain, Noetherian, and local, and assume $R$ is not a field. Let $s \in R$ with $s \neq 0$. Then there exists an ideal $q \subseteq R$ such that $q$ is prime, $s \notin q$, and the Krull dimension of the quotient ring $R / q$, taken as the `ringKrullDim` invariant with values in $\mathbb{N}\cup\{\infty\}$ adjoined with a bottom element, equals $1$. Thus $q$ is a prime of coheight one in $R$ lying in the basic open set $D(s)$; equivalently, in geometric terms, the closed point of $\operatorname{Spec} R$ admits an immediate generisation whose closure meets $D(s)$. No bound on the dimension of $R$ is assumed beyond its being positive (the hypothesis that $R$ is not a field), and no separability or excellence assumption enters.
--
--   This is the standard existence statement for an immediate generisation of the closed point of a Noetherian local domain inside a prescribed basic open set; it is the commutative-algebra input for moving a point of a constructible set to a codimension-one specialisation. It is used in [`AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift`](thm.html#AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift), i.e. in the Noetherian valuative criterion for universal closedness via discrete valuation rings with finite residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (s : R) (hs : s ≠ 0) :
    ∃ q : Ideal R, q.IsPrime ∧ s ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by sorry
