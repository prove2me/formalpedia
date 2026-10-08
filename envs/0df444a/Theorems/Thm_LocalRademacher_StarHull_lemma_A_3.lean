-- Prove2me | Theorems.Thm_LocalRademacher_StarHull_lemma_A_3
-- name    : LocalRademacher.StarHull.lemma_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:08:58.623516+00:00
-- url     : https://prove2.me/theorems/cc33e1df-981e-4bf8-b15f-39c1f4971476
-- title:
--   Lemma A.3, p. 34 — √(u + v) ≤ √u + √v and 2√(uv) ≤ αu + v/α
-- statement:
--   For all real numbers $u, v \ge 0$,
--   $$
--   \sqrt{u + v} \le \sqrt u + \sqrt v,
--   $$
--   and, for every $\alpha > 0$,
--   $$
--   2\sqrt{uv} \le \alpha u + \frac{v}{\alpha}.
--   $$
--
--   The second inequality is used in the last step of the proof of Theorem 3.3 to split the cross term $\sqrt{2 x r^*/n}$ into a multiple of $x/n$ and a multiple of $r^*$.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Lemma A.3, p. 34

import Mathlib

namespace LocalRademacher.StarHull

/-- **Lemma A.3** (p. 34). For `u, v ≥ 0`, `√(u + v) ≤ √u + √v`, and for any `α > 0`,
`2 √(u v) ≤ α u + v / α`. -/
theorem lemma_A_3 :
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → Real.sqrt (u + v) ≤ Real.sqrt u + Real.sqrt v) ∧
      ∀ u v α : ℝ, 0 ≤ u → 0 ≤ v → 0 < α → 2 * Real.sqrt (u * v) ≤ α * u + v / α := by sorry

end LocalRademacher.StarHull
