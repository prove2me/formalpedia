-- Prove2me | Theorems.Thm_FrobeniusEndo_exists_prime_gt_and_quadratic_root
-- name    : FrobeniusEndo.exists_prime_gt_and_quadratic_root
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/dcb7dd3d-04e4-5222-a410-47227e815957
-- title:
--   Roots of X²-aX+q modulo arbitrarily large primes
-- statement:
--   Let $a$ and $q$ be integers with $q \ge 1$, and let $N$ be a natural number. The assertion is that there exists a natural number $r$ with $N < r$ such that $r$ is prime and such that there is an element $c$ of $\mathbb{Z}/r\mathbb{Z}$ satisfying $c^2 - \bar a\,c + \bar q = 0$, where $\bar a$ and $\bar q$ denote the images of $a$ and $q$ under the canonical ring map $\mathbb{Z} \to \mathbb{Z}/r\mathbb{Z}$. Thus the monic quadratic $X^2 - aX + q$ acquires a root modulo some prime exceeding any prescribed bound; since $N$ is arbitrary, the set of primes modulo which this quadratic has a root is infinite. Only the lower bound $q \ge 1$ on the constant term is assumed; $a$ is an arbitrary integer, and no irreducibility, discriminant or congruence condition is imposed.
--
--   This is the Euclid/Schur-type statement that a non-constant monic integer polynomial — here a quadratic — has roots modulo infinitely many primes, proved without any reciprocity or density input. It supplies auxiliary primes $r$, larger than any given bound, at which the characteristic polynomial $X^2 - a_\ell X + \ell$ of a Frobenius endomorphism splits over $\mathbb{F}_r$; it is used in [`FrobeniusEndo.frobCharEqOnPoints_of_line`](thm.html#FrobeniusEndo.frobCharEqOnPoints_of_line).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_exists_prime_gt_and_quadratic_root.lean

import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusEndo.exists_prime_gt_and_quadratic_root (a q : ℤ) (hq : 1 ≤ q) (N : ℕ) : ∃ r : ℕ, N < r ∧ r.Prime ∧ ∃ c : ZMod r, c ^ 2 - (a : ZMod r) * c + (q : ZMod r) = 0 := by sorry
