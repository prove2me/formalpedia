-- Prove2me | Theorems.Thm_GeometricSums_geom_sum_le_bot_Icc
-- name    : GeometricSums.geom_sum_le_bot_Icc
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:47:14.257766+00:00
-- url     : https://prove2.me/theorems/c1f77aae-ad9b-42bf-b45c-34d11cd5e00e
-- title:
--   A geometric sum over an interval is bounded by its first term's tail
-- statement:
--   **A truncated geometric sum starting at $a$ is bounded by the full tail from $a$.**
--
--   For $0 \le r < 1$, $c \ge 0$ and any $a \le b$ (indeed any $a, b$),
--
--   $$\sum_{i=a}^{b} c\,r^{i} \;\le\; \frac{c\,r^{a}}{1-r}.$$
--
--   The right-hand side is the value of the infinite tail $\sum_{i \ge a} c r^{i} = \tfrac{cr^a}{1-r}$,
--   so the content is that every partial sum starting at $a$ is bounded by that tail — true because
--   all terms are non-negative. When $b < a$ the sum is empty and the bound is trivial, so no
--   ordering hypothesis is needed.
--
--   The **bottom-indexed** form is what makes this useful: the bound depends on the starting index
--   $a$ through the factor $r^{a}$, which decays geometrically. In practice one sums over a range
--   $[a,b]$ whose lower endpoint grows, and needs the estimate to inherit that decay rather than
--   collapsing to the uniform bound $c/(1-r)$.
--
--   **Formalization note.** The index set is `Finset.Icc a b`, i.e. $a \le i \le b$; the hypotheses
--   $0 \le c$ and $0 \le r$ ensure all terms are non-negative, and $r < 1$ makes $1 - r > 0$.
-- source:
--   Elementary. Lean proof extracted from `Salt/Tactic/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace GeometricSums

theorem geom_sum_le_bot_Icc {r c : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, c * r ^ i ≤ c * r ^ a / (1 - r) := by sorry

end GeometricSums
