-- Prove2me | Theorems.Thm_ModularCurve_eisensteinTwoCoeff_mul_level
-- name    : ModularCurve.eisensteinTwoCoeff_mul_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/0f63be31-27a6-52c5-b281-16dfdc142c6d
-- title:
--   Invariance of the Eisenstein coefficients under n ↦ np
-- statement:
--   Let $p$ be a prime and $n$ a natural number. For natural numbers $p, m$ write $\sigma'_p(m) = \sum_{d \mid m,\ p \nmid d} d$, the sum of those divisors of $m$ (in the sense of `Nat.divisors`, so empty for $m = 0$) that are not divisible by $p$, and let `eisensteinTwoCoeff p m` be the integer $p - 1$ if $m = 0$ and $24\,\sigma'_p(m)$ otherwise. The theorem asserts the equality of integers
--   $$\mathtt{eisensteinTwoCoeff}\ p\ (np) = \mathtt{eisensteinTwoCoeff}\ p\ n,$$
--   that is, $24\,\sigma'_p(np) = 24\,\sigma'_p(n)$ when $n \neq 0$, and the trivial identity $p - 1 = p - 1$ when $n = 0$ (in which case $np = 0$ as well). No hypothesis beyond the primality of $p$ is imposed; $n$ ranges over all natural numbers, including $0$.
--
--   This is the elementary statement that the coefficient sequence $n \mapsto$ `eisensteinTwoCoeff p n` of the weight-two Eisenstein series attached to level $p$ is fixed by the operator $U_p$ on $q$-expansion coefficients. It is used in [`ModularForm.dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff`](thm.html#ModularForm.dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff), in the analysis of congruences between this Eisenstein series and cusp forms of level $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinTwoCoeff_mul_level.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.eisensteinTwoCoeff_mul_level (p : ℕ) [Fact p.Prime] (n : ℕ) : eisensteinTwoCoeff p (n * p) = eisensteinTwoCoeff p n := by sorry
