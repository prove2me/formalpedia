-- Prove2me | Theorems.Thm_GuthMaynard_ford_exponential_sum_bound
-- name    : GuthMaynard.ford_exponential_sum_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T19:30:29.925211+00:00
-- url     : https://prove2.me/theorems/7a491c58-60f3-486d-822e-4a19f9a76a00
-- title:
--   Ford, Theorem 2 — S(N, t) ≤ 9.463 N^{1−1/(133.66λ²)}, λ = log t / log N
-- statement:
--   For every positive integer $N$, every real $t \ge N$, every $u \in (0, 1]$ and every real $R$ with $N < R \le 2N$,
--   $$\Big|\sum_{N < n \le R}(n+u)^{-it}\Big| \le 9.463\,N^{1 - 1/(133.66\lambda^2)}, \qquad \lambda = \frac{\log t}{\log N}.$$
--
--   This is Theorem 2 of K. Ford, *Vinogradov's integral and bounds for the Riemann zeta function*, Proc. London Math. Soc. (3) 85 (2002) 565–633, https://doi.org/10.1112/S0024611502013655 (arXiv:1910.08209v1, p. 4, whose page numbers are used): “**Theorem 2.** Suppose $N$ is a positive integer, $N \le t$ and set $\lambda = \frac{\log t}{\log N}$. Then $S(N,t) \le 9.463N^{1-1/(133.66\lambda^2)}$.” On the same page, $S(N,t) = \max_{0<u\le1}\max_{N<R\le2N}\Big|\sum_{N<n\le R}(n+u)^{-it}\Big|$, “where $N$ is a positive integer and $t \ge N$”. In Ford's §7 (Lemma 7.3, pp. 66–67), Theorem 2 gives the bound $|\zeta(\sigma+it)| \le At^{B(1-\sigma)^{3/2}}\log^{2/3}t$ of Ford's Theorem 1, which is Richert's bound (1.1). Richert's bound, `GuthMaynard.richert_zeta_bound`, is reduced to this statement.
--
--   **Formalization note.**
--   - The two maxima are written as a bound for every $u$ and every $R$; the sum over $N < n \le R$ runs over the integers $n$ with $N < n \le \lfloor R\rfloor$.
--   - At $N = 1$, $\lambda$ is undefined (division by $\log 1 = 0$). In Lean $\log t / \log 1 = 0$, so the exponent there is $1$ and the bound reads $9.463$. The sum then has at most one term, so this case holds trivially.
-- source:
--   Ford, K., Vinogradov's integral and bounds for the Riemann zeta function, Proc. London Math. Soc. 85 (2002) 565–633, https://doi.org/10.1112/S0024611502013655 (arXiv:1910.08209v1, whose page numbers are used), p. 4, Theorem 2, the input of Richert's bound (1.1) via Ford's §7, Lemma 7.3

import Mathlib

namespace GuthMaynard

theorem ford_exponential_sum_bound :
    ∀ (N : ℕ) (t : ℝ), 1 ≤ N → (N : ℝ) ≤ t → ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∀ R : ℝ, (N : ℝ) < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ≤
          9.463 * (N : ℝ) ^ (1 - 1 / (133.66 * (Real.log t / Real.log N) ^ 2)) := by
  sorry

end GuthMaynard
