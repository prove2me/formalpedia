-- Prove2me | Theorems.Thm_LocalRademacher_StarHull_subroot_growth
-- name    : LocalRademacher.StarHull.subroot_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:28:06.54877+00:00
-- url     : https://prove2.me/theorems/f13da010-2461-477a-8f37-0bed8334bc2c
-- title:
--   Proof of Theorem 3.3 (first part), p. 16 — sub-root growth: ψ(βr) ≤ √β ψ(r) for β ≥ 1
-- statement:
--   Let $\psi$ be a sub-root function: nonnegative and nondecreasing on $[0,\infty)$, with $r \mapsto \psi(r)/\sqrt r$ nonincreasing on $r > 0$. Then for every $\beta \ge 1$ and every $r \ge 0$,
--   $$
--   \psi(\beta r) \le \sqrt{\beta}\, \psi(r).
--   $$
--
--   A sub-root function grows at most like a square root. Applied with $r = r^*$, the fixed point of $\psi$, and $\beta = r/r^*$, it gives $\psi(r) \le \sqrt{r/r^*}\,\psi(r^*) = \sqrt{r r^*}$ for $r \ge r^*$, which is how the complexity term of the error bounds is reduced from $\psi(r)$ to the fixed point $r^*$.
--
--   **Formalization Note** $\psi$ is a function on $\mathbb R$ of which only the values on $[0,\infty)$ are constrained, so the claim is stated for $r \ge 0$. At $r = 0$ it reads $\psi(0) \le \sqrt\beta\,\psi(0)$, which holds because $\psi(0) \ge 0$.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Proof of Theorem 3.3, first part, p. 16, sentence after (3.1)

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

namespace LocalRademacher.StarHull

/-- **Sub-root growth** (Proof of Theorem 3.3, first part, p. 16: "By our assumption it follows
that for `β ≥ 1`, `ψ(βr) ≤ √β ψ(r)`"). If `ψ` is sub-root (Definition 3.1: nonnegative and
nondecreasing on `[0, ∞)`, `r ↦ ψ(r)/√r` nonincreasing on `r > 0`), then for every `β ≥ 1` and
every `r ≥ 0`, `ψ(β r) ≤ √β ψ(r)`. -/
theorem subroot_growth (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) (β r : ℝ) (hβ : 1 ≤ β) (hr : 0 ≤ r) :
    ψ (β * r) ≤ Real.sqrt β * ψ r := by sorry

end LocalRademacher.StarHull
