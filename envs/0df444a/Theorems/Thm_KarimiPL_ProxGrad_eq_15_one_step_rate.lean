-- Prove2me | Theorems.Thm_KarimiPL_ProxGrad_eq_15_one_step_rate
-- name    : KarimiPL.ProxGrad.eq_15_one_step_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:46.574187+00:00
-- url     : https://prove2.me/theorems/6ac5ff2b-5e16-4fc8-a67c-1f9b0f6e8d95
-- title:
--   Eq. (15): one proximal-gradient step contracts $F - F^*$ by $1 - \mu/L$
-- statement:
--   Let $f : \mathbb{R}^d \to \mathbb{R}$ be differentiable and let $g : \mathbb{R}^d \to (-\infty, +\infty]$ be convex with effective domain $D$; write $F = f + g$. Assume:
--
--   1. $L > 0$, and $f$ satisfies the quadratic upper bound (2): for all $x, y \in \mathbb{R}^d$,
--   $$f(y) \le f(x) + \langle \nabla f(x), y - x\rangle + \frac L2 \|y - x\|^2;$$
--   2. $x^* \in D$ minimizes $F$, and $F^* = F(x^*)$;
--   3. $(f, g)$ satisfies the proximal-PL inequality with constant $\mu > 0$: $\frac12\mathcal D_g(x, L) \ge \mu(F(x) - F^*)$ wherever the minimum in $\mathcal D_g(x, L)$ is attained, where
--   $$\mathcal D_g(x,\alpha) = -2\alpha \min_{y} \Big[ \langle \nabla f(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2 + g(y) - g(x) \Big];$$
--   4. $(x_k)_{k\ge0}$ is a run of the proximal-gradient method with step size $1/L$ started at $x_0 \in D$:
--   $$x_{k+1} = \operatorname*{argmin}_y \Big[ \langle \nabla f(x_k), y - x_k\rangle + \frac L2 \|y - x_k\|^2 + g(y) - g(x_k) \Big].$$
--
--   $f$ need not be convex, $g$ need not be closed, and $\mu \le L$ is not assumed.
--
--   Then for every $k \ge 0$
--   $$F(x_{k+1}) - F^* \le \Big(1 - \frac{\mu}{L}\Big)\big[F(x_k) - F^*\big].$$
--
--   This is inequality (15) in the proof of Theorem 5 of Karimi, Nutini and Schmidt; applied recursively it gives the linear rate of Theorem 5.
--
--   **Formalization Note** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` and $\nabla$ is Mathlib's `gradient`. The extended-valued $g$ is encoded by $D$ and real values $g$ on $D$ (`ConvexOn ℝ D g`); each $\operatorname{argmin}$ is a minimizer predicate, and $\min$ in $\mathcal D_g$ is a real infimum that equals the minimum at every point where it is used.
--
--   Differences from the source:
--   - generalization: f has an L-Lipschitz continuous gradient (2) → f differentiable and satisfying inequality (2) for all x, y; reason: an L-Lipschitz gradient implies (2) (milestone eq_2_descent_lemma), so the Lean statement specializes to the literal reading
--   - generalization: proximal-PL inequality (12) at every x → (12) required only at x ∈ dom g where the minimum in (13) is attained (IsProxPL); reason: off dom g (12) reads +∞ ≥ +∞, and where the minimum is not attained (13) is undefined; the Lean hypothesis is implied by the paper's
--   - encoding: g : ℝᵈ → (−∞, ∞] convex, F = f + g → a set D and real values g with ConvexOn ℝ D g; F = f + g on D; reason: every convex extended-valued g has this form and conversely; same instances
--   - encoding: x_{k+1} = argmin_y [⟨∇f(x_k), y − x_k⟩ + (L/2)‖y − x_k‖² + g(y) − g(x_k)] → x (k+1) is a minimizer of that bracket over D (IsProxGradRun); reason: the bracket is strongly convex, so the minimizer is unique when it exists; the method is defined exactly when the predicate holds
--   - encoding: F has a non-empty solution set X*, optimal value F* → x* ∈ D with F(x*) ≤ F(z) for all z ∈ D, and F* = F(x*); reason: F = +∞ off D, so the minimizers of F are exactly these points
--   - encoding: initial point x₀ unrestricted → x 0 ∈ D; reason: for x₀ ∉ dom g the right-hand side (1 − µ/L)^k[F(x₀) − F*] is +∞ or the undefined 0·∞, so the paper's claim has no content there; without x 0 ∈ D the junk real value g(x₀) makes the Lean claim false (d = 1, f ≡ 0, L = 1, D = [0, 1], g = 0 on D, g(2) = −5, x* = 0, µ = 1/2, x₀ = 2, x₁ = 1: at k = 1 it reads 0 ≤ −5/2)
--   - encoding: Lipschitz constant L (implicitly positive) → 0 < L; reason: the step size 1/L and the ratio µ/L require it
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, proof of Theorem 5, eq. (15), p. 9

import Mathlib
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradStep
import Definitions.Def_KarimiPL_ProxGrad_Dg
import Definitions.Def_KarimiPL_ProxGrad_IsProxPL
import Definitions.Def_KarimiPL_ProxGrad_IsProxGradRun

open scoped InnerProductSpace

namespace KarimiPL.ProxGrad

/-- **Eq. (15): one step of the proximal-gradient method contracts `F − F*` by `1 − μ/L`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, proof of Theorem 5, eq. (15), p. 9: "This subsequently implies that
F(xk+1) − F∗ ≤ (1 − µ/L)[F(xk) − F∗], (15) which applied recursively gives the result."

Under the hypotheses of Theorem 5, for every `k ≥ 0`,
`F(x_{k+1}) − F* ≤ (1 − μ/L)(F(x_k) − F*)`.

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`, `∇` is Mathlib's `gradient`.
The paper's `g : ℝᵈ → (−∞, ∞]` is encoded by its effective domain `D` and its finite values
`g` on `D` (`ConvexOn ℝ D g` is the paper's "g is convex"); no closedness or lower
semicontinuity of `g` is assumed. `F(x) = f(x) + g(x)` and `F* = F(x*)`, where `x* ∈ D`
minimizes `F` over `D` (the paper's non-empty solution set). The smoothness hypothesis is (2)
itself, which an `L`-Lipschitz gradient implies (`eq_2_descent_lemma`). The run starts in
`dom g` (`x 0 ∈ D`); off `dom g` the paper's right-hand side is infinite or undefined. `f`
need not be convex and `μ ≤ L` is not assumed. -/
theorem eq_15_one_step_rate {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {L μ : ℝ} (hL : 0 < L) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (hg : ConvexOn ℝ D g)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxD : xstar ∈ D)
    (hmin : ∀ z ∈ D, f xstar + g xstar ≤ f z + g z)
    (hPL : IsProxPL f g D L μ xstar)
    {x : ℕ → EuclideanSpace ℝ (Fin d)} (hx0 : x 0 ∈ D)
    (hrun : IsProxGradRun f g D L x)
    (k : ℕ) :
    f (x (k + 1)) + g (x (k + 1)) - (f xstar + g xstar) ≤
      (1 - μ / L) * (f (x k) + g (x k) - (f xstar + g xstar)) := by sorry

end KarimiPL.ProxGrad
