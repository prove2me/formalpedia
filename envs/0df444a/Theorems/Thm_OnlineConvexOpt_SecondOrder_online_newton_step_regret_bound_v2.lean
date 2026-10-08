-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_online_newton_step_regret_bound_v2
-- name    : OnlineConvexOpt.SecondOrder.online_newton_step_regret_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:30.570781+00:00
-- url     : https://prove2.me/theorems/f9912fff-4c96-4963-9c7b-c7ef80ccdd8b
-- title:
--   Lemma 4.6 — Online Newton step regret via $\sum_t\nabla_t^\top A_t^{-1}\nabla_t$ (corrected regret definition)
-- statement:
--   **Statement (Lemma 4.6).** Let $K$ be a decision set of diameter at most $D$ in a real Hilbert space, and let $f_0,f_1,\dots$ be $\alpha$-exp-concave cost functions on $K$ whose gradients at points of $K$ have norm at most $G$. Run online Newton step (Algorithm 12) with $\gamma=\tfrac12\min\{\tfrac1{GD},\alpha\}$, $\varepsilon=\tfrac1{\gamma^2D^2}$. Then for every horizon $T$,
--   $$\mathrm{Regret}_T(\mathrm{ONS})\le\Bigl(\frac1\alpha+GD\Bigr)\Bigl(\sum_{t=1}^{T}\nabla_t^\top A_t^{-1}\nabla_t+1\Bigr).$$
--
--   **Formalization Note.** The only change from the retired statement is the regret definition: `RegretT` is now the one of `OnlineConvexOpt_FirstOrder_Protocol_v2` (real infimum of the cumulative cost over $K$ instead of the junk-valued `⨅ y ∈ K` binder). Under the hypotheses the infimum is genuine (nonempty $K\ni x_0$, convex costs with bounded gradients at the played points, bounded $K$). $\nabla_t^\top A_t^{-1}\nabla_t$ is `quadForm (A (t+1)).inverse (g t)` in the $0$-indexed convention of `IsOnlineNewtonStep`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 63, Lemma 4.6 (PDF p. 85)

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 4.6 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 63, PDF p. 85). The regret of online Newton step (Algorithm 12, run with
parameters `γ = (1/2) min{1/(GD), α}`, `ε = 1/(γ²D²)` against `α`-exp-concave cost functions `f`
with gradient bound `G` over a decision set `K` of diameter `D`) is bounded by
`Regret_T(ONS) ≤ (1/α + GD)(Σ_{t=1}^T ∇_t^⊤A_t^{-1}∇_t + 1)`, where `∇_t^⊤A_t^{-1}∇_t` is the
quadratic form `quadForm (A (t+1)).inverse (g t)` — the sum runs over the 0-indexed rounds
`t = 0, ..., T - 1`, i.e. the book's `t = 1, ..., T`, matching `A (t + 1)`'s shift in
`IsOnlineNewtonStep`.

Corrected version: `RegretT` is now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret
(genuine infimum over `K`; the retired one returned the junk value `0` outside `K`). Under the
hypotheses the cumulative cost is bounded below on `K` (convexity at the played point `x_0 ∈ K`
plus the gradient and diameter bounds), so the infimum is the book's `min`. -/
theorem online_newton_step_regret_bound_v2
    (K : Set E) (α D G γ ε : ℝ) (f : ℕ → E → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) :
    RegretT K f x T ≤
      (1 / α + G * D) *
        ((∑ t ∈ Finset.range T, quadForm (A (t + 1)).inverse (g t)) + 1) := by sorry

end OnlineConvexOpt.SecondOrder
