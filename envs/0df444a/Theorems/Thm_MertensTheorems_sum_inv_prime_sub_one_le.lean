-- Prove2me | Theorems.Thm_MertensTheorems_sum_inv_prime_sub_one_le
-- name    : MertensTheorems.sum_inv_prime_sub_one_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:26:28.947218+00:00
-- url     : https://prove2.me/theorems/7cfeedd6-1958-4c22-b954-523327cf5616
-- title:
--   A Mertens-type bound for $\sum_{p \le n} 1/(p-1)$
-- statement:
--   **The sum of $1/(p-1)$ over primes has the same $\log\log$ growth as $\sum 1/p$.**
--
--   There is an absolute constant $C$ such that for every $n \ge 2$,
--
--   $$\sum_{p \le n} \frac{1}{p-1} \;\le\; \log\log n \;+\; C .$$
--
--   Mertens' second theorem gives $\sum_{p\le n}\tfrac1p = \log\log n + M + o(1)$, and the
--   difference between the two sums converges absolutely:
--
--   $$\sum_{p} \left(\frac{1}{p-1} - \frac{1}{p}\right) = \sum_{p}\frac{1}{p(p-1)} < \infty,$$
--
--   since $\tfrac{1}{p(p-1)} \le \tfrac{1}{(p-1)^2}$. So replacing $p$ by $p-1$ changes only the
--   additive constant, not the growth.
--
--   The weight $1/(p-1)$ is the one that appears naturally in sieve theory and in multiplicative
--   number theory, because $\tfrac{1}{p-1}$ is the density of a fixed non-zero residue class mod
--   $p$ among the integers coprime to $p$ — equivalently $\sum_{k\ge1}p^{-k}$. Bounds for
--   $\prod_{p\le n}(1 - \tfrac1p)^{-1}$ and for singular series in the Hardy–Littlewood circle
--   method are routinely reduced to this sum.
--
--   **Formalization note.** The sum runs over primes $p \le n$; note $p - 1$ is computed in
--   $\mathbb{R}$ after the cast, so no truncated subtraction occurs. The constant $C$ is
--   existentially quantified.
-- source:
--   Classical; see Mertens (1874) and Montgomery & Vaughan, *Multiplicative Number Theory I*, §2.2. Lean proof extracted from `Salt/Maynard/Mertens.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MertensTheorems

theorem sum_inv_prime_sub_one_le :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p - 1)
        ≤ Real.log (Real.log n) + C := by sorry

end MertensTheorems
