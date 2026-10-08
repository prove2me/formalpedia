-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_ewoo_regret_v2
-- name    : OnlineConvexOpt.SecondOrder.ewoo_regret_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:25.540977+00:00
-- url     : https://prove2.me/theorems/fc1017c2-bd95-437a-b4eb-7b5cb96a0674
-- title:
--   Theorem 4.4 — Logarithmic regret of EWOO for exp-concave losses (corrected regret, $T\ge2$)
-- statement:
--   **Statement (Theorem 4.4).** Let $K\subseteq\mathbb R^n$ ($n\ge1$) be a bounded, measurable, convex set of positive volume, and let $f_0,f_1,\dots$ be $\alpha$-exp-concave cost functions on $K$ ($\alpha>0$). If $x_0,x_1,\dots$ is the play sequence of the Exponentially Weighted Online Optimizer (Algorithm 11) with parameter $\alpha$, then for every horizon $T\ge2$,
--   $$\mathrm{Regret}_T(\mathrm{EWOO})\le\frac n\alpha\log T+\frac2\alpha .$$
--
--   **Formalization Note.** The retired statement used `RegretT` of `OnlineConvexOpt_FirstOrder_Protocol`, whose comparator binder returned the junk value $0$ outside $K$; it now uses `OnlineConvexOpt_FirstOrder_Protocol_v2`, where the comparator is the real infimum of the cumulative cost over $K$ — genuine here, since each $f_t$ is convex on the convex body $K$ and hence bounded below on it. The horizon is restricted to $T\ge2$: the book prints no range, but its proof chooses $\delta=1/T$ and uses $T\log\frac1{1-\delta}\le2$, which is undefined at $T=1$, and the printed bound is in fact false at $T=1$ for $n\ge7$ (EWOO plays the centroid of $K$; for $K$ the standard simplex and $f_0=-\frac1\alpha\log(x_1+\varepsilon)$ the regret tends to $\frac1\alpha\log(n+1)>\frac2\alpha$). For $T\ge2$ the proof is complete as printed. All other hypotheses (standing assumptions of §4.3 made explicit: $K$ bounded, measurable, of positive volume so that the centroid integrals are well defined) are unchanged.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 61, Theorem 4.4 (PDF p. 83) — horizon restricted to T ≥ 2, the range in which the printed proof (δ = 1/T) is valid; the printed statement fails at T = 1 for d ≥ 7

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_EWOO
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open MeasureTheory OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.SecondOrder

/-- Theorem 4.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 61, PDF p. 83). The Exponentially Weighted Online Optimizer (Algorithm
11) run with parameter `α > 0` on `α`-exp-concave cost functions `f` over a bounded, measurable,
convex, `d`-dimensional (`d = n`) decision set `K` of positive volume guarantees, for every
`T ≥ 2`, `Regret_T(EWOO) ≤ (d/α) log T + 2/α`, using
`OnlineConvexOpt.FirstOrder.RegretT` (Eq. (1.2)) for the regret against the same cost functions.

Corrected version: `RegretT` is now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret
(genuine infimum over `K`; the retired one returned the junk value `0` outside `K`). Under the
hypotheses the cumulative cost is bounded below on `K` (each `f_t` is convex on the convex body
`K`), so the infimum is the book's `min`. The horizon is restricted to `T ≥ 2`, where the
book's proof (which sets `δ = 1/T` and uses `T log(1/(1-δ)) ≤ 2`) is valid; the printed
theorem states no range for `T`, but at `T = 1` the displayed bound `2/α` fails for `d ≥ 7`
(EWOO plays the centroid of `K`; for `K` a simplex and `f_1 = -(1/α) log(x_1 + ε)` the regret
tends to `(1/α) log(d+1) > 2/α`). -/
theorem ewoo_regret_v2 (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (hKmeas : MeasurableSet K) (hKvol : 0 < volume K)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hEWOO : IsEWOO K α f x)
    (T : ℕ) (hT : 2 ≤ T) :
    RegretT K f x T ≤ (n / α) * Real.log T + 2 / α := by sorry

end OnlineConvexOpt.SecondOrder
