-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_parametrisation
-- name    : OddPerfectNumber.dris_parametrisation
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T21:16:28.194743+00:00
-- url     : https://prove2.me/theorems/3aed934a-9aba-459a-b4ba-21cde7593771
-- title:
--   Dris parametrisation: $2m^2 = \sigma(p^k)s$ and $\sigma(m^2) = p^k s$
-- statement:
--   Write $\sigma(n)=\sum_{d\mid n} d$ for the sum-of-divisors function.
--
--   Let $p$ be an odd prime, let $k$ be odd and let $m \ge 1$ satisfy the **Euler equation**
--
--   $$\sigma(p^{k})\,\sigma(m^{2}) \;=\; 2\,p^{k}m^{2}.$$
--
--   Then there is a positive integer $s$ — the *Dris index* of the solution — with
--
--   $$2m^{2} = \sigma(p^{k})\,s \qquad\text{and}\qquad \sigma(m^{2}) = p^{k}\,s .$$
--
--   **Context.** By Euler's structure theorem an odd perfect number has the form $N = p^{k}m^{2}$ with $p$ prime, $p \equiv k \equiv 1 \pmod 4$ and $p \nmid m$; multiplicativity of $\sigma$ on the coprime factors $p^{k}$ and $m^{2}$ turns perfection of $N$ into exactly the displayed Euler equation. The two relations above are the standard parametrisation of its solutions: they follow because $p \nmid \sigma(p^{k})$, so $\tfrac12\sigma(p^{k})$ divides $m^{2}$ and $p^{k}$ divides $\sigma(m^{2})$, with the same quotient $s$ in both cases.
--
--   The parametrisation is the starting point for size comparisons between the two parts of an odd perfect number: $s = 1$ holds exactly in the extremal situation $m^{2} \le p^{k}$, and then $\sigma(p^{k}) = 2m^{2}$ and $\sigma(m^{2}) = p^{k}$.
-- source:
--   J. A. B. Dris, 'The abundancy index of divisors of odd perfect numbers', Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (the relations sigma(p^k)/2 | m^2 and p^k | sigma(m^2) with common quotient).

import Mathlib
open Finset

namespace OddPerfectNumber

theorem dris_parametrisation (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 2 = 1)
    (hm : m ≠ 0)
    (heq : (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p ^ k * m ^ 2)) :
    ∃ s : ℕ, 0 < s ∧ 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s := by sorry

end OddPerfectNumber
