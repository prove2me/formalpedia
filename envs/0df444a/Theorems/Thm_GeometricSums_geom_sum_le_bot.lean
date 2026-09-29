-- Prove2me | Theorems.Thm_GeometricSums_geom_sum_le_bot
-- name    : GeometricSums.geom_sum_le_bot
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:47.445311+00:00
-- url     : https://prove2.me/theorems/1cca9186-310b-49bd-a1af-f6678676da83
-- title:
--   A geometric sum over a range is bounded by the full series
-- statement:
--   **Every partial geometric sum is bounded by the value of the full series.**
--
--   For $c \ge 0$ and $0 \le r < 1$, and every $I$,
--
--   $$\sum_{i=0}^{I-1} c\,r^{i} \;\le\; \frac{c}{1-r}.$$
--
--   All terms are non-negative, so the partial sums increase to the limit
--   $\sum_{i \ge 0} c r^{i} = \tfrac{c}{1-r}$ and are therefore bounded by it. The bound is uniform
--   in $I$, which is the point: an estimate obtained this way does not degrade as the truncation
--   length grows.
--
--   This is the workhorse bound whenever a geometric error term is summed over an unspecified
--   number of steps — iterative constructions, dyadic sums, and series comparisons all use it to
--   replace a truncated sum by a closed-form constant.
--
--   **Formalization note.** `Finset.range I` is $\{0,\dots,I-1\}$, so $I = 0$ gives the empty sum;
--   the hypotheses $0 \le r$ and $r < 1$ give both non-negativity of the terms and $1 - r > 0$.
-- source:
--   Elementary. Lean proof extracted from `Salt/Tactic/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace GeometricSums

theorem geom_sum_le_bot {r c : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) (I : ℕ) :
    ∑ i ∈ Finset.range I, c * r ^ i ≤ c / (1 - r) := by sorry

end GeometricSums
