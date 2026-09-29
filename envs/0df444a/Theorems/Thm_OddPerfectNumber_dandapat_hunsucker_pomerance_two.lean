-- Prove2me | Theorems.Thm_OddPerfectNumber_dandapat_hunsucker_pomerance_two
-- name    : OddPerfectNumber.dandapat_hunsucker_pomerance_two
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T06:38:18.339591+00:00
-- url     : https://prove2.me/theorems/50ea38b8-86ee-4a44-9cdc-935bcd69fbcf
-- title:
--   Dandapat–Hunsucker–Pomerance (1975): $\sigma(p^k)=2m^2$ and $\sigma(m^2)=p^k$ are incompatible
-- statement:
--   Write $\sigma(n)=\sum_{d\mid n} d$ for the sum-of-divisors function.
--
--   Let $p$ be a prime, let $k \ge 1$ and let $m$ be odd. Then the pair of equations
--
--   $$\sigma(p^{k}) = 2m^{2}, \qquad \sigma(m^{2}) = p^{k}$$
--
--   has no simultaneous solution.
--
--   **Context.** If $N = p^{k}m^{2}$ is an odd perfect number in Euler form, the Dris parametrisation writes $2m^{2} = \sigma(p^{k})s$ and $\sigma(m^{2}) = p^{k}s$ for a positive integer $s$, the *index* of the solution. The value $s = 1$ is the extremal case $m^{2} \le p^{k}$, and it is exactly the pair of equations displayed above. Suryanarayana asked whether an odd perfect number must satisfy them; the statement here says it cannot, for any exponent $k$, so that every hypothetical odd perfect number has index $s \ge 2$.
--
--   This is the case $t = 2$, $n = m^{2}$ of Theorem 1 of Dandapat, Hunsucker and Pomerance (1975), which determines all solutions of $\sigma(n) = p^{a}$, $\sigma(p^{a}) = tn$: they are $(n,p,a,t) = (21,2,5,3)$ and $n = 2^{c}$, $p = 2^{c+1}-1$, $a = 1$, $t = 2$. Neither is of the above shape with $m$ odd.
-- source:
--   G. G. Dandapat, J. L. Hunsucker and C. Pomerance, Some new results on odd perfect numbers, Pacific J. Math. 57 (1975), 359-364, Theorem 1 and its Corollary (case t = 2, n = m^2; the equations (1) of the introduction, raised as a question by Suryanarayana).

import Mathlib
open Finset

namespace OddPerfectNumber

theorem dandapat_hunsucker_pomerance_two (p k m : ℕ) (hp : p.Prime) (hm : Odd m) (hk : k ≠ 0)
    (h1 : (∑ d ∈ (p ^ k).divisors, d) = 2 * m ^ 2)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ k) : False := by sorry

end OddPerfectNumber
