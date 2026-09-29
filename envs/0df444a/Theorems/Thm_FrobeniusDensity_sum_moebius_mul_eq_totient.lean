-- Prove2me | Theorems.Thm_FrobeniusDensity_sum_moebius_mul_eq_totient
-- name    : FrobeniusDensity.sum_moebius_mul_eq_totient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/93d74764-004f-5eae-b625-147344f277be
-- title:
--   Möbius inversion of Gauss's totient identity
-- statement:
--   For a natural number $n$ with $0 < n$, the sum over the divisors $f$ of $n$ (that is, over `n.divisors`, the finite set of positive divisors of $n$) of $\mu(n/f)\cdot f$, computed in $\mathbb{Z}$ with $\mu$ the Möbius function `ArithmeticFunction.moebius` and with the divisor $f$ cast from $\mathbb{N}$ to $\mathbb{Z}$, equals the integer cast of Euler's totient $\varphi(n)$. Equivalently: $\sum_{f \mid n} \mu(n/f) f = \varphi(n)$ for every $n \geq 1$, i.e. the arithmetic function $\varphi$ is the Dirichlet convolution $\mu * \mathrm{id}$. The positivity hypothesis $0 < n$ is what makes the divisor set and the quotients $n/f$ behave as intended; no further hypotheses occur, and the statement is purely one about natural numbers and integers.
--
--   This is the Möbius inversion of Gauss's identity $\sum_{d \mid n} \varphi(d) = n$, stated as $\varphi = \mu * \mathrm{id}$. It supplies the exact value of the Möbius-weighted mass occurring in the Frobenius density count for a rational conjugacy class, and is used in the Langlands–Tunnell part of the development, in the computation of the tower Dirichlet density attached to elements of order eight.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_sum_moebius_mul_eq_totient.lean

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.sum_moebius_mul_eq_totient (n : ℕ) (hn : 0 < n) :
    ∑ f ∈ n.divisors, (ArithmeticFunction.moebius (n / f)) * (f : ℤ) = (Nat.totient n : ℤ) := by sorry
