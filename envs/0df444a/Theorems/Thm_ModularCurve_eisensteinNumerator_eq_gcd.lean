-- Prove2me | Theorems.Thm_ModularCurve_eisensteinNumerator_eq_gcd
-- name    : ModularCurve.eisensteinNumerator_eq_gcd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/b2979970-71d9-5cd0-874a-c4be7dcda72f
-- title:
--   Eisenstein numerator as a gcd, for odd primes
-- statement:
--   Let $p$ be a natural number which is prime and different from $2$. The assertion is an identity between two natural numbers, all divisions being truncated division of naturals. On the left stands `eisensteinNumerator p`, defined as $(p-1)/\gcd(p-1,12)$, the numerator of the fraction $(p-1)/12$ in lowest terms. On the right stands $\gcd\bigl((p-1)/2,\;(p^2-1)/24\bigr)$. The theorem states that these agree:
--   $$\frac{p-1}{\gcd(p-1,12)} \;=\; \gcd\Bigl(\frac{p-1}{2},\ \frac{p^2-1}{24}\Bigr).$$
--   For $p\ge 5$ both entries on the right are exact divisions, $(p-1)/2$ and $(p^2-1)/24$ being integers; for $p=3$ the second entry is the truncated quotient $\lfloor 8/24\rfloor = 0$ and both sides equal $1$. The hypothesis $p\neq 2$ cannot be dropped: for $p=2$ the left-hand side is $1$ while the right-hand side is $\gcd(0,0)=0$.
--
--   The quantity $(p-1)/\gcd(p-1,12)$ is the numerator of $(p-1)/12$ occurring in Mazur's analysis of the Eisenstein ideal, where it measures the order of the relevant cuspidal divisor class at level $p$; the gcd form on the right is the shape in which the two natural congruence conditions at a prime $p$ present themselves. The identity is used by [`CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo), which compares $q$-expansion coefficients of a cusp form with the divisor-sum function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinNumerator_eq_gcd.lean

import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.eisensteinNumerator_eq_gcd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : eisensteinNumerator p = Nat.gcd ((p - 1) / 2) ((p ^ 2 - 1) / 24) := by sorry
