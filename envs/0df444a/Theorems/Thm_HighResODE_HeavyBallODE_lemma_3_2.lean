-- Prove2me | Theorems.Thm_HighResODE_HeavyBallODE_lemma_3_2
-- name    : HighResODE.HeavyBallODE.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:13.450139+00:00
-- url     : https://prove2.me/theorems/228fbfd1-d641-46b5-a590-dea885952ddd
-- title:
--   Lemma 3.2, p. 14 — for f ∈ S²_{μ,L} and s > 0, the Lyapunov function (3.3) satisfies dE/dt ≤ −(√μ/4)E
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ with minimizer $x^\star$, let $s>0$ be any step size, and let $(X,\dot X)$ be the solution of the high-resolution heavy-ball ODE (1.10) started at $x_0$. Then the Lyapunov function
--   $$\mathcal E(t)=\bigl(1+\sqrt{\mu s}\bigr)\bigl(f(X)-f(x^\star)\bigr)+\frac14\|\dot X\|^2+\frac14\bigl\|\dot X+2\sqrt{\mu}\,(X-x^\star)\bigr\|^2$$
--   is differentiable at every $t\ge0$ (from the right at $t=0$) and
--   $$\frac{d\mathcal E(t)}{dt}\le-\frac{\sqrt\mu}{4}\,\mathcal E(t).$$
--
--   This is the decay inequality behind the linear convergence of the heavy-ball ODE; note that it holds for every step size $s>0$, without the restriction $s\le1/L$.
--
--   **Formalization Note.** The derivative is taken within $[0,\infty)$, and the claim is stated as the existence of a number that is this derivative and satisfies the bound, so the inequality cannot hold merely because a derivative is undefined. A minimizer is a point $x^\star$ with $f(x^\star)\le f(z)$ for all $z$; the solution is any pair $(X,V)$ satisfying (1.10) with its initial conditions, which is the paper's "the" solution since that solution is unique.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 14, Lemma 3.2 (proof in App. B.1, p. 50)

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace HighResODE.HeavyBallODE

theorem lemma_3_2 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t → ∃ e' : ℝ, HasDerivWithinAt (lyap f μ s xs X V) e' (Set.Ici 0) t ∧
      e' ≤ -(Real.sqrt μ / 4) * lyap f μ s xs X V t := by sorry

end HighResODE.HeavyBallODE
