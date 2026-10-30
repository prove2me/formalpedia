-- Prove2me | Theorems.Thm_KarimiPL_ProxGrad_one_step_decrease
-- name    : KarimiPL.ProxGrad.one_step_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:09.965896+00:00
-- url     : https://prove2.me/theorems/155de307-3b86-4a5a-965f-6c200a0511fe
-- title:
--   Proof of Theorem 5, p. 9: one step decreases $F$ by $\mathcal D_g(x,L)/(2L)$
-- statement:
--   Let $f : \mathbb{R}^d \to \mathbb{R}$ be differentiable and let $g : \mathbb{R}^d \to (-\infty, +\infty]$ have effective domain $D$; write $F = f + g$. Let $L > 0$ and suppose $f$ satisfies the quadratic upper bound (2):
--   $$f(y) \le f(x) + \langle \nabla f(x), y - x\rangle + \frac L2 \|y - x\|^2 \quad \text{for all } x, y.$$
--   Let $x \in \mathbb{R}^d$ and let $p$ be a proximal-gradient step from $x$ with step size $1/L$,
--   $$p \in \operatorname*{argmin}_y \Big[ \langle \nabla f(x), y - x\rangle + \frac L2 \|y - x\|^2 + g(y) - g(x) \Big].$$
--   Then
--   $$F(p) \le F(x) - \frac{1}{2L}\mathcal D_g(x, L),$$
--   where $\mathcal D_g(x,\alpha) = -2\alpha \min_{y} \big[ \langle \nabla f(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2 + g(y) - g(x) \big]$.
--
--   This is the sufficient-decrease step in the proof of Theorem 5 of Karimi, Nutini and Schmidt (first three lines of the display on p. 9); combined with the proximal-PL inequality it yields the one-step contraction (15).
--
--   **Formalization Note** The extended-valued $g$ is encoded by $D$ and real values on $D$; the argmin is a minimizer predicate, and $\mathcal D_g$ is a real infimum, equal to the minimum here because $p$ attains it.
--
--   Differences from the source:
--   - generalization: f has an L-Lipschitz continuous gradient (2) → f differentiable and satisfying inequality (2) for all x, y; reason: an L-Lipschitz gradient implies (2) (milestone eq_2_descent_lemma), so the Lean statement specializes to the literal reading
--   - generalization: stated at an iterate x_k ∈ dom g under all hypotheses of Theorem 5 → any x ∈ ℝᵈ and any minimizer p; no convexity of g, no X*, no (12); reason: the display uses only (2) and the definition of x_{k+1}, and the constant g(x) cancels; the Lean statement specializes to the paper's step
--   - encoding: g : ℝᵈ → (−∞, ∞], F = f + g → a set D and real values g on D; reason: every extended-valued g has this form; same instances
--   - encoding: x_{k+1} = argmin_y [⟨∇f(x_k), y − x_k⟩ + (L/2)‖y − x_k‖² + g(y) − g(x_k)] → p is a minimizer of that bracket over D (IsProxGradStep); reason: the paper's x_{k+1} is exactly such a minimizer
--   - encoding: Lipschitz constant L (implicitly positive) → 0 < L; reason: the step size 1/L and the ratio µ/L require it
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, proof of Theorem 5, unnumbered display (lines 1–3), p. 9

import Mathlib
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep
import Definitions.Def_KarimiPL_ProxGrad_Dg

open scoped InnerProductSpace

namespace KarimiPL.ProxGrad

/-- **Proof of Theorem 5, p. 9: one proximal-gradient step decreases `F` by `Dg(x, L)/(2L)`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, proof of Theorem 5, unnumbered display (first three lines), p. 9:
"F(xk+1) = f(xk+1) + g(xk) + g(xk+1) − g(xk)
≤ F(xk) + ⟨∇f(xk), xk+1 − xk⟩ + (L/2)||xk+1 − xk||² + g(xk+1) − g(xk)
≤ F(xk) − (1/(2L))Dg(xk, L)".

Let `L > 0`, let `f` be differentiable and satisfy (2) with constant `L`, and let `p` attain
the minimum of (13) at `x` with `α = L` (the update (14)). Then
`f(p) + g(p) ≤ f(x) + g(x) − (1/(2L)) Dg(x, L)`.

**Formalization Note.** The paper's extended-valued `g` is encoded by its effective domain `D`
and its finite values `g` on `D`. The paper states this at an iterate `x_k ∈ dom g`; here
`x` is arbitrary, because the constant `g(x)` cancels on both sides. Hypothesis (2) is assumed
directly (an `L`-Lipschitz gradient implies it, see `eq_2_descent_lemma`). Convexity of `g` is
not needed for this step and is not assumed. -/
theorem one_step_decrease {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {L : ℝ} (hL : 0 < L) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    {x p : EuclideanSpace ℝ (Fin d)} (hp : IsProxGradStep f g D L x p) :
    f p + g p ≤ f x + g x - 1 / (2 * L) * Dg f g D L x := by sorry

end KarimiPL.ProxGrad
