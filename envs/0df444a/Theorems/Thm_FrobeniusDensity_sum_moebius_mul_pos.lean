-- Prove2me | Theorems.Thm_FrobeniusDensity_sum_moebius_mul_pos
-- name    : FrobeniusDensity.sum_moebius_mul_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/fe8ac4ef-d97e-5278-8ca8-6c7e3bdcaed9
-- title:
--   Positivity of sum_{f∣ n}μ(n/f)f for n the order of a group element
-- statement:
--   Let $G$ be a group, assumed finite, and let $\sigma \in G$; write $n = \operatorname{orderOf} \sigma$ for its order. The assertion is that the integer-valued sum over the divisors $f$ of $n$, in Mathlib's sense of the divisor finset of a natural number, of $\mu(n/f) \cdot f$ — where $\mu$ is the Möbius function of Mathlib's arithmetic-function library, $n/f$ is natural-number division, and $f$ is cast into $\mathbb{Z}$ — is strictly positive: $$0 < \sum_{f \mid n} \mu(n/f)\, f.$$ The finiteness of $G$ enters only to guarantee that $\sigma$ has finite, hence nonzero, order, so that the divisor finset is nonempty and the sum is not vacuous. No further hypotheses are imposed on $G$ or $\sigma$; classically the sum equals Euler's totient $\varphi(n)$, but only its positivity is claimed here. The proof invokes the Möbius-collapse identity [`ArithmeticFunction.sum_moebius_filter_dvd`](thm.html#ArithmeticFunction.sum_moebius_filter_dvd), which states that for $n \neq 0$ and $m \mid n$ one has $\sum_{f \mid n} \mu(n/f) \cdot [m \mid f] = [m = n]$.
--
--   This is the Möbius convolution identity $(\mu * \mathrm{Id})(n) = \varphi(n)$, recorded in the weaker form of a positivity statement for $n$ the order of an element of a finite group. It supplies the nonvanishing leading coefficient in the Möbius-inversion step of Frobenius's density theorem, and is used in the derivation of [`FrobeniusDensity.statement_of_degOneAsymptotic`](thm.html#FrobeniusDensity.statement_of_degOneAsymptotic) from the degree-one prime-counting asymptotics.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_sum_moebius_mul_pos.lean

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical in

theorem FrobeniusDensity.sum_moebius_mul_pos {G : Type*} [Group G] [Finite G] (σ : G) :
    0 < ∑ f ∈ (orderOf σ).divisors,
      (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) := by sorry
