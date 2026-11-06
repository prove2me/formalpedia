-- Prove2me | Theorems.Thm_GuthMaynard_sum_endpoint_term_le
-- name    : GuthMaynard.sum_endpoint_term_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T02:42:36.80154+00:00
-- url     : https://prove2.me/theorems/138dd230-8e84-43fb-a20e-9a704c993bdb
-- title:
--   Averaging the B-process endpoint terms over e ∈ (N/2, 4N]
-- statement:
--   There is an absolute constant $C > 0$ such that for every integer $N \ge 1$ and every real $u \ge 1$,
--   $$\sum_{\lfloor N/2\rfloor < e \le 4N}\frac{A}{1 + A\,\big\|\frac{u}{2\pi e}\big\|} \le C\,N\Big(1 + \log(u+2) + \frac Nu\Big), \qquad A = \frac{8N}{\sqrt u},$$
--   where $\|x\| = |x - \mathrm{round}(x)|$ is the distance from $x$ to a nearest integer.
--
--   Each summand is, up to a factor $2$, $\min(A, 1/\|u/2\pi e\|)$: the endpoint term of the B-process (`GuthMaynard.norm_sum_cpow_sub_dual_window_le`) for an interval with endpoint $e$. One such term can be as large as $A = 8N/\sqrt u$. On average over $e$, however, it is $O(1 + \log(u+2) + N/u)$.
--
--   **Formalization note.** This is an auxiliary step, not a claim of Jutila's paper. It belongs to a proof of Jutila's large values estimate (1.2) at $q = 1$ (`GuthMaynard.card_le_of_large_values_jutila_q_one`; M. Jutila, *Zero-density estimates for $L$-functions*, Acta Arith. 32 (1977) 55–62, https://doi.org/10.4064/aa-32-1-55-62). There the endpoints of the summation intervals are averaged through a smoothed majorant, playing the role of Jutila's smooth weight $b(n)$ on p. 57.
-- source:
--   Jutila, M., Zero-density estimates for L-functions, Acta Arith. 32 (1977) 55–62, https://doi.org/10.4064/aa-32-1-55-62, p. 56, an auxiliary step (averaging of the B-process endpoint terms) of a proof of (1.2) at q = 1

import Mathlib

namespace GuthMaynard

theorem sum_endpoint_term_le : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : ℝ, 1 ≤ u →
    ∑ e ∈ Finset.Ioc (N / 2) (4 * N),
      (8 * N / Real.sqrt u) / (1 + (8 * N / Real.sqrt u) *
        |u / (2 * Real.pi * e) - round (u / (2 * Real.pi * e))|) ≤
      C * N * (1 + Real.log (u + 2) + N / u) := by
  sorry

end GuthMaynard
