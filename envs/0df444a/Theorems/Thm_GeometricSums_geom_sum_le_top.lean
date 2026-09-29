-- Prove2me | Theorems.Thm_GeometricSums_geom_sum_le_top
-- name    : GeometricSums.geom_sum_le_top
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:34.188696+00:00
-- url     : https://prove2.me/theorems/6e0f5f37-015f-4996-96a0-5c978549a852
-- title:
--   A geometric sum over a range with ratio above one
-- statement:
--   **For ratio $r>1$, a geometric sum over $\{0,\dots,I-1\}$ is controlled by $r^{I}$.**
--
--   For $c \ge 0$, $r > 1$ and every $I$,
--
--   $$\sum_{i=0}^{I-1} c\,r^{i} \;\le\; \frac{c\,r^{I}}{r-1}.$$
--
--   Exact summation gives $c\,\tfrac{r^{I}-1}{r-1}$, and dropping the $-1$ yields the bound. The
--   essential feature is that the answer is a constant multiple of the **largest** term $r^{I-1}$,
--   with constant $\tfrac{r}{r-1}$ — for an increasing geometric progression the total is
--   comparable to its final term, uniformly in the length.
--
--   This is the estimate behind "the top scale dominates" in dyadic and multi-scale arguments: an
--   error growing geometrically across scales contributes, in total, no more than a constant times
--   its contribution at the largest scale.
--
--   **Formalization note.** `Finset.range I` is $\{0,\dots,I-1\}$, so $I = 0$ gives the empty sum
--   and the bound holds trivially; $r > 1$ makes $r - 1 > 0$.
-- source:
--   Elementary. Lean proof extracted from `Salt/Tactic/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace GeometricSums

theorem geom_sum_le_top {r c : ℝ} (hc : 0 ≤ c) (hr : 1 < r) (I : ℕ) :
    ∑ i ∈ Finset.range I, c * r ^ i ≤ c * r ^ I / (r - 1) := by sorry

end GeometricSums
