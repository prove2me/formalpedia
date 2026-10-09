-- Prove2me | Theorems.Thm_NesterovODE_Rate_energy_hasDerivAt
-- name    : NesterovODE.Rate.energy_hasDerivAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:46.141717+00:00
-- url     : https://prove2.me/theorems/eb0870dc-3373-4579-96f7-f851fd260bcf
-- title:
--   p. 7, proof of Theorem 3 — Ė = 2t(f(X) − f⋆) + t²⟨∇f, Ẋ⟩ + 4⟨X + (t/2)Ẋ − x⋆, (3/2)Ẋ + (t/2)Ẍ⟩
-- statement:
--   Let $f\in\mathcal F_\infty$ on $\mathbb R^n$, let $x^\star$ be a minimizer of $f$ with $f^\star=f(x^\star)$, and let $X$ be a solution of the ODE (3), $\ddot X+\frac3t\dot X+\nabla f(X)=0$, with $X(0)=x_0$, $\dot X(0)=0$. Let $\mathcal E(t)=t^2(f(X(t))-f^\star)+2\|X(t)+t\dot X(t)/2-x^\star\|^2$.
--
--   Then for every $t>0$ the energy is differentiable at $t$, with
--   $$\dot{\mathcal E}(t)=2t\big(f(X)-f^\star\big)+t^2\langle\nabla f(X),\dot X\rangle+4\Big\langle X+\frac t2\dot X-x^\star,\ \frac32\dot X+\frac t2\ddot X\Big\rangle,$$
--   where $X,\dot X,\ddot X$ are evaluated at $t$.
--
--   This is the first step of the proof of Theorem 3: the derivative of the energy before the ODE is used.
--
--   **Formalization Note** $\ddot X(t)$ enters as any vector $A$ with $\dot X$ differentiable at $t$ with derivative $A$; along a solution this $A$ is $-\frac3t\dot X(t)-\nabla f(X(t))$.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 7, proof of Theorem 3 (display after the definition of the energy)

import Mathlib
import Definitions.Def_NesterovODE_Rate_Setting

namespace NesterovODE.Rate

/-- Proof of Theorem 3, p. 7: along a solution of (3), for every `t > 0` and every value `A` of
`Ẍ(t)`, the energy has derivative
`Ė = 2t(f(X) − f⋆) + t²⟨∇f(X), Ẋ⟩ + 4⟨X + (t/2)Ẋ − x⋆, (3/2)Ẋ + (t/2)Ẍ⟩`. -/
theorem energy_hasDerivAt {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar ≤ f y)
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V)
    (t : ℝ) (ht : 0 < t) (A : EuclideanSpace ℝ (Fin n)) (hA : HasDerivAt V A t) :
    HasDerivAt (energy f xstar X V)
      (2 * t * (f (X t) - f xstar) + t ^ 2 * inner ℝ (gradient f (X t)) (V t)
        + 4 * inner ℝ (X t + (t / 2) • V t - xstar) ((3 / 2 : ℝ) • V t + (t / 2) • A)) t := by sorry

end NesterovODE.Rate
