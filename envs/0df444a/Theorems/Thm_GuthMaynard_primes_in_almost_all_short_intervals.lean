-- Prove2me | Theorems.Thm_GuthMaynard_primes_in_almost_all_short_intervals
-- name    : GuthMaynard.primes_in_almost_all_short_intervals
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T18:14:36.496281+00:00
-- url     : https://prove2.me/theorems/8b6ce540-35e3-45f4-a618-7d3c939f0b0b
-- title:
--   Corollary 1.4 (Count of primes in 'almost-all' short intervals)
-- statement:
--   There is a constant $C'$ such that for every $\varepsilon > 0$ there are constants $C$ and $X_0$ with the following property. For all $X \ge X_0$ and all $y \in [X^{2/15+\varepsilon}, X^{0.99}]$, the number of integers $x$ with $\lceil X\rceil \le x \le \lfloor 2X\rfloor$ for which
--   $$\Big|\pi(x+y) - \pi(x) - \frac{y}{\log x}\Big| > C\,y\exp\big(-(\log x)^{1/4}\big)$$
--   is at most $C' X\exp(-(\log X)^{1/4})$. Here $\pi(z)$ is `Nat.primeCounting ⌊z⌋₊`.
--
--   **Formalization note.**
--   - The count of exceptions is printed as $O(X\exp(-\sqrt[4]{\log x}))$, with the bound variable $x$ inside it. It is read as $O(X\exp(-\sqrt[4]{\log X}))$, the only reading in which the count is a number.
--   - Its implied constant carries no subscript $\epsilon$, so $C'$ is chosen before $\varepsilon$.
--   - The error term's $O_\epsilon$ is the constant $C$, which depends on $\varepsilon$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 3, Corollary 1.4 (Count of primes in 'almost-all' short intervals)

import Mathlib

namespace GuthMaynard

theorem primes_in_almost_all_short_intervals :
    ∃ C' : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ y : ℝ,
      y ∈ Set.Icc (X ^ (2 / 15 + ε)) (X ^ (0.99 : ℝ)) →
      ((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter fun x : ℕ =>
          C * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) <
            |((Nat.primeCounting ⌊(x : ℝ) + y⌋₊ : ℝ) - Nat.primeCounting x) - y / Real.log x|).card ≤
        C' * X * Real.exp (-Real.log X ^ (1 / 4 : ℝ)) := by
  sorry

end GuthMaynard
