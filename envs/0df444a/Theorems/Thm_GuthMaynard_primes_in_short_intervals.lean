-- Prove2me | Theorems.Thm_GuthMaynard_primes_in_short_intervals
-- name    : GuthMaynard.primes_in_short_intervals
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T18:14:22.346707+00:00
-- url     : https://prove2.me/theorems/7d6674fc-11cc-4a16-942e-a4962ab2bd4a
-- title:
--   Corollary 1.3 (Count of primes in short intervals)
-- statement:
--   For every $\varepsilon > 0$ there are constants $C$ and $x_0$ such that for all $x \ge x_0$ and all $y \in [x^{17/30+\varepsilon}, x^{0.99}]$,
--   $$\Big|\pi(x+y) - \pi(x) - \frac{y}{\log x}\Big| \le C\,y\exp\big(-(\log x)^{1/4}\big),$$
--   where $\pi(z)$ is the number of primes at most $z$ (`Nat.primeCounting ⌊z⌋₊`).
--
--   **Formalization note.** $O_\varepsilon$ is read as a constant depending on $\varepsilon$, valid for all large $x$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 2–3, Corollary 1.3 (Count of primes in short intervals)

import Mathlib

namespace GuthMaynard

theorem primes_in_short_intervals :
    ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      y ∈ Set.Icc (x ^ (17 / 30 + ε)) (x ^ (0.99 : ℝ)) →
      |((Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊) - y / Real.log x| ≤
        C * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) := by
  sorry

end GuthMaynard
