-- Prove2me | Theorems.Thm_OnlineConvexOpt_FirstOrder_online_gradient_descent_regret_v2
-- name    : OnlineConvexOpt.FirstOrder.online_gradient_descent_regret_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:22:05.213996+00:00
-- url     : https://prove2.me/theorems/e681e836-deaa-4603-a227-33ddeff1ff53
-- title:
--   Theorem 3.1 — Online gradient descent regret bound (corrected regret definition)
-- statement:
--   **Statement (Theorem 3.1).** Let $K$ be a convex, complete, nonempty subset of a real Hilbert space with diameter at most $D$ ($\operatorname{dist}(x,y)\le D$ for all $x,y\in K$), and let $f_0,f_1,\dots$ be cost functions, each convex on $K$ and with every gradient at a point of $K$ of norm at most $G$ (the book's $G$, p. 20: a bound on the (sub)gradient norms over $K$). Run online gradient descent (Algorithm 8) with step sizes $\eta_t = D/(G\sqrt{t+1})$ (the book's $\eta_{t+1}=D/(G\sqrt{t+1})$ under the $0$-indexed shift). Then for every horizon $T\ge 1$,
--   $$\mathrm{Regret}_T=\sum_{t=1}^{T} f_t(x_t)-\min_{x^\star\in K}\sum_{t=1}^{T} f_t(x^\star)\le \tfrac32\,GD\sqrt{T}.$$
--
--   **Formalization Note.** The retired version used the regret definition `OnlineConvexOpt.FirstOrder.RegretT` of `OnlineConvexOpt_FirstOrder_Protocol`, whose comparator `⨅ y ∈ K, …` evaluates on $\mathbb R$ to the junk value $\inf\emptyset=0$ at every $y\notin K$, so the subtracted term was $\le 0$ for every bounded $K$ and the statement was false (constant costs on a singleton). The new statement imports `OnlineConvexOpt_FirstOrder_Protocol_v2`, where `RegretT` subtracts $\inf\{\sum_{t<T} f_t(y) : y\in K\}$ (the real infimum of the image of $K$). Under the theorem's standing hypotheses — $K$ nonempty with diameter $\le D$, $f_t$ convex on $K$ with a gradient of norm $\le G$ at the played point $x_t\in K$ — the cumulative cost is bounded below on $K$ by $\sum_t f_t(x_t) - TGD$, so this infimum is the book's $\min_{x^\star\in K}$ (an infimum rather than an attained minimum when $K$ is merely closed and bounded in an infinite-dimensional space; the bound holds against every comparator in $K$ either way). Rounds are indexed $0,\dots,T-1$; $G$ bounds the norm of the gradient at every point of $K$ where $f_t$ is differentiable (the run predicate forces differentiability at the played points, which is all the proof uses); $K$ convex, complete, nonempty and the diameter bound are §2.1's standing assumptions made explicit. No other change from the retired statement.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 43, Theorem 3.1 (PDF p. 65)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

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

`K` (convex, complete, nonempty, diameter `≤ D`) and the costs `f`, convex on `K` with gradient
norm bounded by `G` on `K` (book p. 20, PDF 42), are the chapter-wide standing hypotheses of
§2.1/§2.2, stated as explicit hypotheses. Corrected version: `RegretT` is now the
`OnlineConvexOpt_FirstOrder_Protocol_v2` regret, whose comparator is the genuine infimum over
`K` (the retired definition's `⨅ y ∈ K` binder returned the junk value `0` outside `K`). Under
these hypotheses the cumulative cost is bounded below on `K` (convexity at `x_0 ∈ K` plus the
gradient bound and the diameter bound), so the infimum is the book's `min`. -/
theorem online_gradient_descent_regret_v2
    (hKconv : Convex ℝ K) (hKcomplete : IsComplete K) (hKne : K.Nonempty)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (hGpos : 0 < G) (hDpos : 0 < D)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, η t = D / (G * Real.sqrt (t + 1)))
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f η x g)
    (T : ℕ) (hT : 1 ≤ T) :
    RegretT K f x T ≤ (3 / 2) * G * D * Real.sqrt T := by sorry

end OnlineConvexOpt.FirstOrder
