-- Prove2me | Theorems.Thm_OnlineConvexOpt_FirstOrder_online_gradient_descent_strongly_convex_regret
-- name    : OnlineConvexOpt.FirstOrder.online_gradient_descent_strongly_convex_regret
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-18T05:19:06.178602+00:00
-- url     : https://prove2.me/theorems/05cad211-adce-441c-a7e3-4ba71fcbeb67
-- title:
--   Theorem 3.3 — Logarithmic regret for strongly convex costs
-- statement:
--   **Statement (Theorem 3.3).** With the same standing hypotheses on $K$ as Theorem 3.1, suppose every cost function $f_t$ is $\alpha$-strongly convex on $K$ (for a common $\alpha > 0$) and has gradient norm at most $G$ on $K$ (the book's definition of $G$, p. 20). Run online gradient descent (Algorithm 8) with step sizes $\eta_t = 1/(\alpha(t+1))$. Then for every $T \ge 1$,
--   $$\mathrm{Regret}_T \le \frac{G^2}{2\alpha}(1 + \log T).$$
--
--   Strong convexity of the losses — a property stronger than mere convexity but weaker than the smoothness used for offline convergence rates — lets the same algorithm, with only the step-size schedule changed, achieve regret logarithmic in $T$ instead of $O(\sqrt{T})$. The proof again uses the Pythagorean projection inequality, but now combines it with the strong-convexity inequality $2(f_t(x_t) - f_t(x^\star)) \le 2\nabla_t^\top(x_t - x^\star) - \alpha\|x^\star - x_t\|^2$, which cancels the $\alpha \|x^\star - x_t\|^2$ term against the projection bound's telescoping difference exactly, leaving only $\sum_t \eta_t G^2 = (G^2/\alpha)\sum_t 1/(t+1) \le (G^2/\alpha)(1 + \log T)$.
--
--   **Formalization Note.** As in Theorem 3.1, rounds are 0-indexed, so the step size at round $t$ is $1/(\alpha(t+1))$, the book's $\eta_{t+1} = 1/(\alpha(t+1))$ under the shift. `StrongConvexOn K α (f t)` is Mathlib's uniform-convexity-modulus notion of $\alpha$-strong convexity, equivalent on an inner product space to $x \mapsto f(x) - \tfrac{\alpha}{2}\|x\|^2$ being convex. $G$ is stated as a bound on the gradient's norm on $K$ (via `HasGradientAt`), matching the book's own definition rather than the weaker two-point Lipschitz condition. `D` does not appear among this theorem's hypotheses or its stated bound, matching the book, which does not mention `D` in Theorem 3.3.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 47, Theorem 3.3 (PDF p. 69)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

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

`K` (convex, complete, nonempty) and the costs `f`, convex with subgradient norm bounded by `G`
on `K` (book p. 20, PDF 42: `G` bounds `‖∇f(x)‖` over `K`, not a Lipschitz constant — a stronger
hypothesis than plain `G`-Lipschitzness), are the chapter-wide standing hypotheses of §2.1/§2.2
(the diameter bound `D` is not needed for this bound, matching the book, which does not mention
`D` in Theorem 3.3), stated here as explicit hypotheses of the theorem (not left as unused
ambient `variable`s) so they are genuinely part of its formal content. -/
theorem online_gradient_descent_strongly_convex_regret
    (hKconv : Convex ℝ K) (hKcomplete : IsComplete K) (hKne : K.Nonempty) (hGpos : 0 < G)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (α : ℝ) (hα : 0 < α) (hfSC : ∀ t, StrongConvexOn K α (f t))
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, η t = 1 / (α * (t + 1)))
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f η x g)
    (T : ℕ) (hT : 1 ≤ T) :
    RegretT K f x T ≤ (G ^ 2 / (2 * α)) * (1 + Real.log T) := by sorry

end OnlineConvexOpt.FirstOrder
