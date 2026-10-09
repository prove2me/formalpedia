-- Prove2me | Theorems.Thm_NesterovODE_Rate_energy_deriv_nonpos
-- name    : NesterovODE.Rate.energy_deriv_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:28.981086+00:00
-- url     : https://prove2.me/theorems/ddd0eaa1-2c8a-4ebf-a639-fe4ecd69fc8c
-- title:
--   p. 8, proof of Theorem 3 — Ė = 2t(f(X) − f⋆) − 2t⟨X − x⋆, ∇f(X)⟩ ≤ 0
-- statement:
--   Let $f\in\mathcal F_\infty$ on $\mathbb R^n$, let $x^\star$ be a minimizer of $f$ with $f^\star=f(x^\star)$, let $X$ be a solution of (3) with $X(0)=x_0$, $\dot X(0)=0$, and let $\mathcal E$ be the energy of Theorem 3's proof. Then for every $t>0$, $\mathcal E$ is differentiable at $t$ and
--   $$\dot{\mathcal E}(t)=2t\big(f(X)-f^\star\big)+4\Big\langle X-x^\star,-\frac t2\nabla f(X)\Big\rangle=2t\big(f(X)-f^\star\big)-2t\langle X-x^\star,\nabla f(X)\rangle\le 0,$$
--   with $X=X(t)$.
--
--   The identity comes from substituting $\frac32\dot X+\frac t2\ddot X=-\frac t2\nabla f(X)$, which is the ODE (3); the inequality is the convexity of $f$. Together they say that the energy is nonincreasing on $(0,\infty)$.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 8, proof of Theorem 3 (first display)

import Mathlib
import Definitions.Def_NesterovODE_Rate_Setting

namespace NesterovODE.Rate

/-- Proof of Theorem 3, p. 8: substituting `3Ẋ/2 + tẌ/2 = −t∇f(X)/2` (the ODE (3)), the energy
has derivative `Ė = 2t(f(X) − f⋆) + 4⟨X − x⋆, −t∇f(X)/2⟩ = 2t(f(X) − f⋆) − 2t⟨X − x⋆, ∇f(X)⟩`
at every `t > 0`, and this is `≤ 0` by convexity of `f`. -/
theorem energy_deriv_nonpos {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar ≤ f y)
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (energy f xstar X V)
        (2 * t * (f (X t) - f xstar)
          + 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t))) t ∧
      2 * t * (f (X t) - f xstar) + 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t))
        = 2 * t * (f (X t) - f xstar) - 2 * t * inner ℝ (X t - xstar) (gradient f (X t)) ∧
      2 * t * (f (X t) - f xstar) - 2 * t * inner ℝ (X t - xstar) (gradient f (X t)) ≤ 0 := by sorry

end NesterovODE.Rate
