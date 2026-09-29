-- Prove2me | Theorems.Thm_GeometricSums_geom_sum_le_top_Icc
-- name    : GeometricSums.geom_sum_le_top_Icc
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:46.016996+00:00
-- url     : https://prove2.me/theorems/676ba821-306d-4afa-ad21-60d50c3691e1
-- title:
--   A geometric sum with ratio above one is bounded by its last term
-- statement:
--   **For ratio $r>1$ a geometric sum is dominated by a constant times its largest term.**
--
--   For $c \ge 0$, $r > 1$ and any $a, b$,
--
--   $$\sum_{i=a}^{b} c\,r^{i} \;\le\; \frac{c\,r^{\,b+1}}{r-1}.$$
--
--   When $r > 1$ the terms **increase**, so the sum is dominated by its top end — the mirror image
--   of the $r < 1$ case, where the bound is governed by the first term. Summing the geometric
--   progression exactly gives $c\,\tfrac{r^{b+1}-r^{a}}{r-1}$, and dropping the subtracted term
--   yields the stated bound.
--
--   The form matters in dyadic decompositions: a quantity growing geometrically across scales has
--   total size comparable to its largest scale, with the constant $1/(r-1)$ measuring how much the
--   lower scales contribute. That is the standard justification for "the last dyadic block
--   dominates".
--
--   **Formalization note.** The index set is `Finset.Icc a b`, so $b < a$ gives the empty sum and
--   the bound holds trivially; $r > 1$ makes $r - 1 > 0$.
-- source:
--   Elementary. Lean proof extracted from `Salt/Tactic/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace GeometricSums

theorem geom_sum_le_top_Icc {r c : ℝ} (hc : 0 ≤ c) (hr : 1 < r) (a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, c * r ^ i ≤ c * r ^ (b + 1) / (r - 1) := by sorry

end GeometricSums
