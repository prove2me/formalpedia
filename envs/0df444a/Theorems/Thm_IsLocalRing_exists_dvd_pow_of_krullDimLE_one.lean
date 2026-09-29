-- Prove2me | Theorems.Thm_IsLocalRing_exists_dvd_pow_of_krullDimLE_one
-- name    : IsLocalRing.exists_dvd_pow_of_krullDimLE_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/8056f92a-790b-52f7-9c34-a426b63b1694
-- title:
--   Nonzero elements divide powers of maximal-ideal elements
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and a local ring, and assume $R$ has Krull dimension at most one (`Ring.KrullDimLE 1 R`). Let $b \in R$ be nonzero, and let $c$ be an element of the maximal ideal of $R$. Then there exists a natural number $n$ such that $b \mid c^n$. Equivalently, the maximal ideal of $R$ is contained in the radical of the principal ideal $bR$ for every nonzero $b$; no hypothesis $b \in \mathfrak m$ is imposed, the unit case being covered by $n = 0$.
--
--   This is the standard consequence of the rank-one hypothesis in a local domain: since the only primes are $0$ and $\mathfrak m$, every nonzero element of $\mathfrak m$ is "topologically nilpotent" relative to any other, i.e. $\sqrt{bR} = \mathfrak m$ for $b \in \mathfrak m \setminus \{0\}$. It is used in the study of regular prolongations along algebraic curves, in the two results on representing elements with small valuation, respectively residues of elements of an intersection of residue spans, by images of algebra maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocalRing.exists_dvd_pow_of_krullDimLE_one
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by sorry
