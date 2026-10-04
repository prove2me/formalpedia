-- Prove2me | Theorems.Thm_NumStochOpt_ListScheduling_eq_8_10_makespan_sandwich
-- name    : NumStochOpt.ListScheduling.eq_8_10_makespan_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T20:58:34.392547+00:00
-- url     : https://prove2.me/theorems/de116494-dfb7-43d6-aa77-6979f543db7a
-- title:
--   Eq. (8.10) — $\sum p_j/m \le C^*_n(m) \le C^H_n(m) \le \sum p_j/m + p_{\max}$, divided by $n\mu/m$
-- statement:
--   Let $p_1, \dots, p_n \ge 0$ be processing times, $n \ge 1$, let $m \ge 1$ be the number of identical machines and $\mu > 0$. Write $S_n = \sum_{j=1}^n p_j$, $p_{\max} = \max_{j \le n} p_j$, $C^*_n(m)$ for the minimum makespan and $C^H_n(m)$ for the makespan of list scheduling. Then
--
--   $$
--   \frac{S_n - n\mu}{n\mu} + 1 \;\le\; \frac{C^*_n(m)}{n\mu/m} \;\le\; \frac{C^H_n(m)}{n\mu/m} \;\le\; \frac{S_n - n\mu}{n\mu} + 1 + \frac{m\, p_{\max}}{n\mu}.
--   $$
--
--   This is the deterministic sandwich $S_n/m \le C^*_n(m) \le C^H_n(m) \le S_n/m + p_{\max}$ divided by $n\mu/m$: the averaging lower bound on the optimum, and the list-scheduling upper bound. Every probabilistic result of the mission is obtained by controlling the two error terms on its right-hand side.
--
--   **Formalization Note** The inequality is deterministic; $\mu$ is any positive number here (in the book it is the mean processing time). Processing times are 0-based: $S_n$ is `∑ j ∈ Finset.range n, p j`.
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 206, Eq. (8.10)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule

namespace NumStochOpt.ListScheduling

/-- Eq. (8.10), p. 206: for nonnegative processing times, `n ≥ 1` jobs, `m ≥ 1` machines and
`μ > 0`, with `S = ∑_{j<n} p j`,
`(S - nμ)/(nμ) + 1 ≤ C*_n(m)/(nμ/m) ≤ C^H_n(m)/(nμ/m) ≤ (S - nμ)/(nμ) + 1 + m p_max/(nμ)`. -/
theorem eq_8_10_makespan_sandwich (n m : ℕ) (p : ℕ → ℝ) (μ : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hn : 1 ≤ n) (hm : 1 ≤ m) (hμ : 0 < μ) :
    ((∑ j ∈ Finset.range n, p j) - n * μ) / (n * μ) + 1
        ≤ optMakespan n m p / (n * μ / m) ∧
      optMakespan n m p / (n * μ / m) ≤ listMakespan n m p / (n * μ / m) ∧
      listMakespan n m p / (n * μ / m)
        ≤ ((∑ j ∈ Finset.range n, p j) - n * μ) / (n * μ) + 1
            + m * maxProcTime n p / (n * μ) := by sorry

end NumStochOpt.ListScheduling
