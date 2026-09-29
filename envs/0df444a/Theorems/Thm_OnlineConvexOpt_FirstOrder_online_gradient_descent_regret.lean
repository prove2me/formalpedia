-- Prove2me | Theorems.Thm_OnlineConvexOpt_FirstOrder_online_gradient_descent_regret
-- name    : OnlineConvexOpt.FirstOrder.online_gradient_descent_regret
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-18T05:09:33.854074+00:00
-- url     : https://prove2.me/theorems/d2671c40-3cf2-415d-8b74-35f35483b7a0
-- title:
--   Theorem 3.1 — Online gradient descent regret bound
-- statement:
--   **Statement (Theorem 3.1).** Let $K$ be a convex, complete, nonempty subset of a real inner product space with diameter at most $D$ (i.e. $\operatorname{dist}(x, y) \le D$ for all $x, y \in K$), and let $f_0, f_1, \dots$ be convex cost functions on $K$ whose gradients, where they exist, have norm at most $G$ on $K$ (i.e. $\|\nabla f_t(x)\| \le G$ for every $x \in K$ — the book's definition of $G$, p. 20, a bound on the subgradient norm, not merely a Lipschitz constant). Run online gradient descent (Algorithm 8) with step sizes $\eta_t = D / (G\sqrt{t+1})$. Then for every horizon $T \ge 1$,
--   $$\mathrm{Regret}_T = \sum_{t=1}^{T} f_t(x_t) - \min_{x^\star \in K} \sum_{t=1}^{T} f_t(x^\star) \le \frac{3}{2} G D \sqrt{T}.$$
--
--   This is the book's central result: the simplest general-purpose online convex optimization algorithm already achieves the (worst-case-optimal, by Theorem 3.2) $O(\sqrt{T})$ regret rate, with the explicit constant $3/2$. The proof combines convexity ($f_t(x_t) - f_t(x^\star) \le \nabla_t^\top(x_t - x^\star)$), the Pythagorean projection inequality bounding $\|x_{t+1} - x^\star\|^2$, a telescoping sum over rounds, and the chosen step-size schedule.
--
--   **Formalization Note.** Rounds are indexed $0, \dots, T-1$ (`Finset.range T`) rather than the book's $1, \dots, T$; the step size at (0-indexed) round $t$ is stated as $\eta_t = D/(G\sqrt{t+1})$, i.e. the book's $\eta_{t+1} = D/(G\sqrt{t+1})$ under the shift. $D$ and $G$ are the chapter-wide diameter and gradient-norm bounds, carried as shared hypotheses via `variable`, not per-theorem parameters; $G$ is stated as a bound on the gradient's norm at points of $K$ (via Mathlib's `HasGradientAt`), matching the book's own definition rather than the weaker two-point Lipschitz condition. `RegretT`, the metric projection, and the online-gradient-descent run predicate are from `OnlineConvexOpt.FirstOrder.Protocol`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 43, Theorem 3.1 (PDF p. 65)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (K : Set E) (D G : ℝ) (f : ℕ → E → ℝ)

namespace OnlineConvexOpt.FirstOrder

/-- Theorem 3.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 43, PDF p. 65). Online gradient descent (Algorithm 8) with step sizes
`η_t = D / (G √t)` (`t ∈ [T]` in the book's 1-indexed rounds; here `η` at round `t`, in the
0-indexed convention of `RegretT`, is the book's `η_{t+1} = D / (G √(t+1))`) guarantees, for
every `T ≥ 1`,
`Regret_T = Σ_{t=1}^T f_t(x_t) - min_{x⋆ ∈ K} Σ_{t=1}^T f_t(x⋆) ≤ (3/2) G D √T`.

`K` (convex, complete, nonempty, diameter `≤ D`) and the costs `f`, convex with subgradient norm
bounded by `G` on `K` (book p. 20, PDF 42: `G` bounds `‖∇f(x)‖` over `K`, not a Lipschitz
constant — a stronger hypothesis than plain `G`-Lipschitzness), are the chapter-wide standing
hypotheses of §2.1/§2.2, stated here as explicit hypotheses of the theorem (not left as unused
ambient `variable`s) so they are genuinely part of its formal content. -/
theorem online_gradient_descent_regret
    (hKconv : Convex ℝ K) (hKcomplete : IsComplete K) (hKne : K.Nonempty)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (hGpos : 0 < G) (hDpos : 0 < D)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, η t = D / (G * Real.sqrt (t + 1)))
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f η x g)
    (T : ℕ) (hT : 1 ≤ T) :
    RegretT K f x T ≤ (3 / 2) * G * D * Real.sqrt T := by sorry

end OnlineConvexOpt.FirstOrder
