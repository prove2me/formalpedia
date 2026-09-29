-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_online_newton_step_regret_bound
-- name    : OnlineConvexOpt.SecondOrder.online_newton_step_regret_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:34:09.414645+00:00
-- url     : https://prove2.me/theorems/2d2ec12f-5800-48ae-ac40-c5862a82d0b5
-- title:
--   Lemma 4.6 — the online Newton step regret-to-matrix-sum reduction
-- statement:
--   Let $K$ be a decision set of diameter $D$ in a real inner-product space, let
--   $f_0, f_1, \dots$ be $\alpha$-exp-concave, $G$-gradient-bounded cost functions on $K$, and
--   run online Newton step (Algorithm 12) with $\gamma = \tfrac12\min\{1/(GD), \alpha\}$ and
--   $\varepsilon = 1/(\gamma^2 D^2)$, producing decisions $x_t$, gradients $\nabla_t$, and
--   running matrices $A_t$. Then for every horizon $T$,
--   $$
--   \mathrm{Regret}_T(\mathrm{ONS}) \;\le\; \Bigl(\frac1\alpha + GD\Bigr)
--     \left(\sum_{t=1}^T \nabla_t^\top A_t^{-1} \nabla_t \;+\; 1\right) .
--   $$
--   This is the key reduction of the chapter: it converts the regret bound into a sum of
--   quadratic forms $\nabla_t^\top A_t^{-1}\nabla_t$ that the running matrix's own definition
--   makes telescope (Theorem 4.5 bounds this sum by $n \log T$ via a log-determinant argument).
--   The proof follows the same generalized-Pythagorean template as online gradient descent's
--   regret bound, but in the norm induced by $A_t$ rather than the Euclidean norm, which is
--   exactly why online Newton step needs the generalized projection of Algorithm 12 in place of
--   the ordinary metric projection.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 63, PDF p. 85, Lemma 4.6

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

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
`IsOnlineNewtonStep`. -/
theorem online_newton_step_regret_bound
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
