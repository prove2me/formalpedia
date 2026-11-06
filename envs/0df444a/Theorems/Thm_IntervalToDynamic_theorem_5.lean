-- Prove2me | Theorems.Thm_IntervalToDynamic_theorem_5
-- name    : IntervalToDynamic.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:45.781201+00:00
-- url     : https://prove2.me/theorems/1a1f228a-5a75-4700-96f3-9d753535dba0
-- title:
--   Theorem 5 — instantaneous regret transfer $f(x)-f(u)\le h(y)-h(u)$
-- statement:
--   Suppose Assumptions 1 and 2 hold for the selected loss class, and let $\mathcal Y=\mathcal B(D_{\mathcal X})$. Let $h$ be the surrogate of Eqs. (10)–(12) built from $y$, with the parameters of Table 2. Then for every $y\in\mathcal Y$ and every $u\in\mathcal X$, with $x=\Pi_{\mathcal X}[y]$,
--   $$
--   f(x)-f(u)\le h(y)-h(u).
--   $$
--
--   Regret on the original losses is thus bounded, round by round, by regret on the surrogates over the larger domain.
--
--   Differences from the source:
--   - generalization: f_t differentiable on the domain, with gradient ∇f_t → any gradient oracle with `HasGradientWithinAt` on the domain; reason: the domain may have empty interior; the gradient of a differentiable loss is such an oracle, so the printed case is included
--   - encoding: X compact convex, with Π_X and X^T presupposing a point → `X.Nonempty` inside `SatisfiesAssumptions`; reason: Π_X and comparators in X need a point; no instance of the paper is excluded
--   - encoding: for every t ∈ [T], with f_t, x_t, y_t, u_t, h_t → one round: a loss `f`, an oracle `gr`, and `y`, `u`; reason: the statement is pointwise in t, and applies to every round
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 5, p.10

import Mathlib
import Definitions.Def_IntervalToDynamic_roundLoss
import Definitions.Def_IntervalToDynamic_SatisfiesAssumptions

namespace IntervalToDynamic

/-- Theorem 5 (instantaneous regret transfer). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Theorem 5, p.10.

Under Assumptions 1 and 2 for the selected loss class, with the parameters of Table 2, the surrogate
`h` of Eqs. (10)–(12) satisfies, for every `y ∈ Y = B(D_X)` and every `u ∈ X`,
`f(x) − f(u) ≤ h(y) − h(u)`, where `x = Π_X[y]`.

**Formalization Note.** One round, for one loss `f` with gradient oracle `gr`; no run and no
algorithm are involved. -/
theorem theorem_5 {d : ℕ} (hd : 0 < d) (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (gr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hAss : SatisfiesAssumptions mode X DX G f gr)
    (y u : EuclideanSpace ℝ (Fin d)) (hy : y ∈ Metric.closedBall 0 DX) (hu : u ∈ X) :
    f (proj X y) - f u ≤ roundLoss mode X DX G gr y y - roundLoss mode X DX G gr y u := by sorry

end IntervalToDynamic
