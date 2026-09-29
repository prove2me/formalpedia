-- Prove2me | Theorems.Thm_OnlineConvexOpt_ConvexBasics_constrained_gd_well_conditioned_convergence
-- name    : OnlineConvexOpt.ConvexBasics.constrained_gd_well_conditioned_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T18:35:59.247071+00:00
-- url     : https://prove2.me/theorems/4b972257-57bd-4727-b27d-656b2a01bef1
-- title:
--   Theorem 2.6 — linear convergence for well-conditioned functions
-- statement:
--   **Statement (Theorem 2.6, the goal).** Let $K \subseteq E$ be convex, $f$ $\alpha$-strongly convex and $\beta$-smooth on $K$ (so $\gamma := \alpha/\beta$ is $f$'s condition number, and $f$ is called $\gamma$-well-conditioned), and let $x^\star \in K$ minimize $f$ over $K$. Run constrained gradient descent (Algorithm 4) on $K$ with the constant step size $\eta_t = 1/\beta$, and write $h_x := f(x) - f(x^\star)$. Then, in the book's 1-indexed rounds (round $1$ is the algorithm's input $x_1$),
--   $$h_{t+1} \le h_1 \cdot e^{-\gamma t / 4} \qquad \text{for every } t \ge 0.$$
--
--   This is the chapter's capstone: for the best-conditioned class of functions the book considers, projected gradient descent converges *linearly* (the optimality gap shrinks by a constant multiplicative factor every round, rather than polynomially in $t$), with an explicit rate governed entirely by the condition number $\gamma$. The proof combines the potential-function relations of Lemma 2.4 with the projection's contraction property to show the gap contracts by a factor of $1 - \gamma/4$ each round, then bounds $(1-\gamma/4)^t \le e^{-\gamma t/4}$.
--
--   **Formalization Note.** `x` is 0-indexed, with `x 0` the book's initial point $x_1$, so `x k` is the book's $x_{k+1}$; the book's $h_{t+1} \le h_1 e^{-\gamma t/4}$ therefore becomes `f (x t) - f xstar ≤ (f (x 0) - f xstar) * Real.exp (-(α/β) * t / 4)` for every `t : ℕ`, matching the round shift exactly (at `t = 0` this reads `h(x 0) ≤ h(x 0)`, the book's own trivial base case `h_1 ≤ h_1`). $\gamma$ is not introduced as a separate variable; it is written out as $\alpha/\beta$ at each occurrence, per the book's own definition. `StronglyConvexOn`/`SmoothOn` are taken over `K` itself (not all of $E$), since this is the constrained setting of §2.3.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 27, Theorem 2.6 (PDF p. 49)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_ConstrainedGradientDescent
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_OnlineConvexOpt_ConvexBasics_SmoothOn

namespace OnlineConvexOpt.ConvexBasics

/-- Theorem 2.6 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 27, PDF p. 49). For constrained minimization of `γ`-well-conditioned
functions (`γ = α / β`, the condition number of `f`) with `η_t = 1 / β`, Algorithm 4
(`IsConstrainedGradientDescent`) converges as `h_{t+1} ≤ h_1 · e^{-γt/4}`. `x` is 0-indexed
(the book's round `1` is `x 0`, so `x s` is the book's `x_{s+1}`), and correspondingly the
book's `h_{t+1}` (round `t + 1`) is `f (x t) - f x⋆` here and the book's `h_1` (round `1`) is
`f (x 0) - f x⋆`: the goal is `h (x t) ≤ h (x 0) · e^{-γt/4}` for every `t : ℕ`, where
`h_s := f(x_s) - f(x⋆)`. -/
theorem constrained_gd_well_conditioned_convergence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hK : Convex ℝ K) (f : E → ℝ) (g : E → E) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : StronglyConvexOn K f g α) (hsm : SmoothOn K f g β)
    (xstar : E) (hxstarK : xstar ∈ K) (hxstar : IsMinOn f K xstar)
    (x : ℕ → E) (hGD : IsConstrainedGradientDescent K f g β x) (t : ℕ) :
    f (x t) - f xstar ≤ (f (x 0) - f xstar) * Real.exp (-(α / β) * t / 4) := by sorry

end OnlineConvexOpt.ConvexBasics
