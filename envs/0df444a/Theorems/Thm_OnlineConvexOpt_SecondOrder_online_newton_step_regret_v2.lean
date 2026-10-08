-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_online_newton_step_regret_v2
-- name    : OnlineConvexOpt.SecondOrder.online_newton_step_regret_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:30.387981+00:00
-- url     : https://prove2.me/theorems/b4123c39-3e3f-4fd4-815a-ea473dc57a48
-- title:
--   Theorem 4.5 — Online Newton step logarithmic regret bound (corrected regret definition)
-- statement:
--   **Statement (Theorem 4.5).** Let $K\subseteq\mathbb R^n$ ($n\ge2$) be a decision set of diameter at most $D$, and let $f_0,f_1,\dots$ be $\alpha$-exp-concave cost functions on $K$ whose gradients at points of $K$ have norm at most $G$. Run online Newton step (Algorithm 12) with $\gamma=\tfrac12\min\{\tfrac1{GD},\alpha\}$ and $\varepsilon=\tfrac1{\gamma^2D^2}$. Then for every $T\ge4$,
--   $$\mathrm{Regret}_T\le 2\Bigl(\frac1\alpha+GD\Bigr)n\log T .$$
--
--   **Formalization Note.** The only change from the retired statement is the regret definition: `RegretT` is now the one of `OnlineConvexOpt_FirstOrder_Protocol_v2`, which subtracts the real infimum of the cumulative cost over $K$ (the retired `⨅ y ∈ K` binder returned the junk value $0$ outside $K$, so the statement was false for constant positive costs). Under the hypotheses the infimum is genuine: $K\ni x_0$ is nonempty, and each $f_t$ is convex on $K$ with a gradient of norm $\le G$ at $x_t\in K$ and $K$ has diameter $\le D$. The literal range "$n>1$, $T\ge4$" of the book's derivation is kept (`hn : 2 ≤ n`); rounds are $0$-indexed with $A_{t+1}$ built from rounds $0,\dots,t$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 63, Theorem 4.5 (PDF p. 85)

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.SecondOrder

/-- Theorem 4.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 63, PDF p. 85). Online Newton step (Algorithm 12) on `α`-exp-concave
cost functions `f`, `G`-gradient-bounded, over a decision set `K` of diameter `D` in
`n`-dimensional space, run with `γ = (1/2) min{1/(GD), α}`, `ε = 1/(γ²D²)`, guarantees for
every `T ≥ 4`, `Regret_T ≤ 2(1/α + GD) n log T`. (The book's own derivation, immediately
following the proof, states the bound "for `n > 1`, `T ≥ 4`"; `hn : 2 ≤ n` records that
literally.)

Corrected version: `RegretT` is now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret
(genuine infimum over `K`; the retired one returned the junk value `0` outside `K`). Under the
hypotheses the cumulative cost is bounded below on `K` (convexity at the played point `x_0 ∈ K`
plus the gradient and diameter bounds), so the infimum is the book's `min`; `K` is nonempty
since `x 0 ∈ K`. -/
theorem online_newton_step_regret_v2 (n : ℕ) (hn : 2 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (α D G : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (γ ε : ℝ) (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) (hT : 4 ≤ T) :
    RegretT K f x T ≤ 2 * (1 / α + G * D) * n * Real.log T := by sorry

end OnlineConvexOpt.SecondOrder
