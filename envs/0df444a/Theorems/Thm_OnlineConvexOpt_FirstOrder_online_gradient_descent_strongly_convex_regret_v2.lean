-- Prove2me | Theorems.Thm_OnlineConvexOpt_FirstOrder_online_gradient_descent_strongly_convex_regret_v2
-- name    : OnlineConvexOpt.FirstOrder.online_gradient_descent_strongly_convex_regret_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:44.019217+00:00
-- url     : https://prove2.me/theorems/6697e7dc-9ec0-4b01-8afb-b22aa6e7f867
-- title:
--   Theorem 3.3 — Logarithmic regret of OGD for strongly convex losses (corrected regret definition)
-- statement:
--   **Statement (Theorem 3.3).** Let $K$ be a convex, complete, nonempty subset of a real Hilbert space and let $f_0,f_1,\dots$ be cost functions that are convex and $\alpha$-strongly convex on $K$ (for a common $\alpha>0$), with every gradient at a point of $K$ of norm at most $G$. Run online gradient descent (Algorithm 8) with step sizes $\eta_t = 1/(\alpha(t+1))$ (the book's $\eta_{t+1}=1/(\alpha(t+1))$ under the $0$-indexed shift). Then for every $T\ge1$,
--   $$\mathrm{Regret}_T\le \frac{G^2}{2\alpha}\,(1+\log T).$$
--
--   **Formalization Note.** The retired version used `OnlineConvexOpt.FirstOrder.RegretT` of `OnlineConvexOpt_FirstOrder_Protocol`, whose comparator `⨅ y ∈ K, …` evaluates to the junk value $0$ at every $y\notin K$, so the subtracted term was $\le 0$ for every bounded $K$ and the statement was false. The new statement imports `OnlineConvexOpt_FirstOrder_Protocol_v2`, whose `RegretT` subtracts the real infimum of $\{\sum_{t<T}f_t(y): y\in K\}$. Under the hypotheses this infimum is genuine: $f_t$ is $\alpha$-strongly convex on $K$ with gradient $g_t$ at $x_t\in K$, so $f_t(y)\ge f_t(x_t)+\langle g_t,y-x_t\rangle+\tfrac\alpha2\|y-x_t\|^2$ is bounded below on $K$ without any diameter bound (matching the book, which does not mention $D$ in Theorem 3.3). `StrongConvexOn K α` is Mathlib's $\alpha$-strong convexity; rounds are $0$-indexed; $G$ bounds the gradient norm at every point of $K$ where $f_t$ is differentiable. No other change from the retired statement.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 47, Theorem 3.3 (PDF p. 69)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (K : Set E) (G : ℝ) (f : ℕ → E → ℝ)

namespace OnlineConvexOpt.FirstOrder

/-- Theorem 3.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 47, PDF p. 69). For `α`-strongly convex loss functions, online gradient
descent (Algorithm 8) with step sizes `η_t = 1/(αt)` (`t ∈ [T]` in the book's 1-indexed rounds;
here `η` at round `t`, in the 0-indexed convention of `RegretT`, is the book's
`η_{t+1} = 1 / (α(t+1))`) achieves, for every `T ≥ 1`,
`Regret_T ≤ (G² / (2α)) (1 + log T)`.

`K` (convex, complete, nonempty) and the costs `f`, convex with gradient norm bounded by `G`
on `K` (book p. 20, PDF 42) and `α`-strongly convex on `K`, are the chapter-wide standing
hypotheses of §2.1/§2.2 (the diameter bound `D` is not needed for this bound, matching the book,
which does not mention `D` in Theorem 3.3). Corrected version: `RegretT` is now the
`OnlineConvexOpt_FirstOrder_Protocol_v2` regret, whose comparator is the genuine infimum over
`K` (the retired definition's `⨅ y ∈ K` binder returned the junk value `0` outside `K`). Under
these hypotheses the cumulative cost is bounded below on `K` (strong convexity at `x_0 ∈ K`
plus the gradient bound there), so the infimum is the book's `min`. -/
theorem online_gradient_descent_strongly_convex_regret_v2
    (hKconv : Convex ℝ K) (hKcomplete : IsComplete K) (hKne : K.Nonempty) (hGpos : 0 < G)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (α : ℝ) (hα : 0 < α) (hfSC : ∀ t, StrongConvexOn K α (f t))
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, η t = 1 / (α * (t + 1)))
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f η x g)
    (T : ℕ) (hT : 1 ≤ T) :
    RegretT K f x T ≤ (G ^ 2 / (2 * α)) * (1 + Real.log T) := by sorry

end OnlineConvexOpt.FirstOrder
