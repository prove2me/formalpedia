-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_ewoo_regret
-- name    : OnlineConvexOpt.SecondOrder.ewoo_regret
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:33:28.253901+00:00
-- url     : https://prove2.me/theorems/0e4cdb23-66b6-4489-890e-eebaa6c416de
-- title:
--   Theorem 4.4 — regret of the Exponentially Weighted Online Optimizer
-- statement:
--   Let $K \subseteq \mathbb{R}^n$ be a bounded, measurable, convex set of positive volume, and
--   let $f_0, f_1, \dots$ be $\alpha$-exp-concave cost functions on $K$ (for a fixed
--   $\alpha > 0$). If $x_0, x_1, \dots$ is the play sequence of the Exponentially Weighted
--   Online Optimizer (Algorithm 11) run with parameter $\alpha$, then for every horizon
--   $T \ge 1$,
--   $$
--   \mathrm{Regret}_T(\mathrm{EWOO}) \;\le\; \frac{n}{\alpha}\log T + \frac{2}{\alpha} ,
--   $$
--   where $\mathrm{Regret}_T = \sum_{t=1}^T f_t(x_t) - \min_{x^\star \in K}\sum_{t=1}^T
--   f_t(x^\star)$ is the usual online-convex-optimization regret. This bound is logarithmic in
--   $T$ — a qualitative improvement over the $O(\sqrt T)$ regret of first-order methods on
--   general convex losses — and, unlike the online Newton step bound of Theorem 4.5, involves
--   no Lipschitz constant or diameter bound on $K$ at all; its cost is instead computational,
--   since a literal implementation of EWOO's defining integral takes exponential time in $n$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 61, PDF p. 83, Theorem 4.4

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_EWOO
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.SecondOrder

/-- Theorem 4.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 61, PDF p. 83). The Exponentially Weighted Online Optimizer (Algorithm
11) run with parameter `α > 0` on `α`-exp-concave cost functions `f` over a bounded, measurable,
convex, `d`-dimensional (`d = n`) decision set `K` of positive volume guarantees, for every
`T ≥ 1`, `Regret_T(EWOO) ≤ (d/α) log T + 2/α`, using
`OnlineConvexOpt.FirstOrder.RegretT` (Eq. (1.2)) for the regret against the same cost functions.
-/
theorem ewoo_regret (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (hKmeas : MeasurableSet K) (hKvol : 0 < volume K)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hEWOO : IsEWOO K α f x)
    (T : ℕ) (hT : 1 ≤ T) :
    RegretT K f x T ≤ (n / α) * Real.log T + 2 / α := by sorry

end OnlineConvexOpt.SecondOrder
