-- Prove2me | Theorems.Thm_ModernOnlineLearning_SaddlePoint_theorem_7_47_linear
-- name    : ModernOnlineLearning.SaddlePoint.theorem_7_47_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:29.96207+00:00
-- url     : https://prove2.me/theorems/651984d9-4292-40d9-8e2a-93a4ce5f655b
-- title:
--   Theorem 7.47, pp. 129–130 — optimistic FTRL regret for linear losses and a fixed regularizer
-- statement:
--   Let $V$ be nonempty, closed and convex in a real normed space, let $\psi$ be $\lambda$-strongly convex on $V$ with $\lambda>0$, and let $z_t$ be an optimistic FTRL run for linear losses $g_t(z)$ and the previous-vector hints $g_{t-1}(z)$, with $g_0=0$. Let $T\ge1$, and let $z_{T+1}$ be a minimizer over $V$ of $\psi+\sum_{i=1}^T g_i$ (the next FTRL point with a zero hint); for $t<T$, $z_{t+1}$ is the run's own iterate. For every $u\in V$, the specialization of Theorem 7.47 gives both bounds
--   $$
--   \sum_{t=1}^T g_t(z_t-u)\le\psi(u)-\psi(z_1)+\sum_{t=1}^T\left[(g_t-g_{t-1})(z_t-z_{t+1})-\frac{\lambda}{2}\|z_t-z_{t+1}\|^2\right]
--
--   $$
--   and, separately,
--   $$
--   \sum_{t=1}^T g_t(z_t-u)\le\psi(u)-\psi(z_1)+\sum_{t=1}^T\frac{\|g_t-g_{t-1}\|_*^2}{2\lambda}.
--   $$
--   This is the regret input for the two players in Algorithm 15.6.
--
--   **Formalization Note** This milestone states precisely the linear-loss, fixed-regularizer instance used on p. 262. The general theorem also treats time-varying nonlinear losses and regularizers. Given an already specified run, existence and uniqueness of its minimizers are not part of this instance. The theorem does not define $x_{T+1}$; its proof (p. 130) sets the hint of round $T+1$ equal to that of round $T$. With that choice the first inequality is false: for $V=\mathbb R$, $\psi(z)=z^2/2$, $\lambda=1$, $T=2$, $g_1=1$, $g_2=0$, $u=-1$, the left side is $1$ and the right side is $1/2$. The proof's telescoping argument is correct when the hint at round $T+1$ is zero, so $z_{T+1}$ is the minimizer of $\psi+\sum_{i\le T}g_i$. The second inequality does not involve $z_{T+1}$.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 7.47, pp. 129–130, linear-loss fixed-regularizer instance; application in §15.5, pp. 261–262

import Mathlib
import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false

namespace ModernOnlineLearning.SaddlePoint

/-- Theorem 7.47, p. 129–130, specialized to linear losses and a fixed regularizer.
For `t < T` the point `x_(t+1)` of the bound is the run's own iterate `z (t+1)`.
The look-ahead point `x_(T+1)` is `w`, a minimizer over `V` of `ψ + Σ_(i ≤ T) g_i`,
i.e. the hint at round `T + 1` is zero. The proof on p. 130 sets the hint at `T + 1` to the
hint at `T` instead; with that choice the first inequality fails (`V = ℝ`, `ψ z = z²/2`,
`λ = 1`, `T = 2`, `g₁ = 1`, `g₂ = 0`, `u = −1`: left side `1`, right side `1/2`), while with
the zero hint the proof goes through. -/
theorem theorem_7_47_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Set E) (ψ : E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (z : ℕ → E)
    (lam : ℝ) (T : ℕ) (u : E) (hT : 1 ≤ T)
    (hVne : V.Nonempty) (hVclosed : IsClosed V) (hu : u ∈ V) (hlam : 0 < lam) (hstrong : StrongConvexOn V lam ψ)
    (hrun : IsOptFTRLRun V ψ g z T) (w : E)
    (hw : IsMinOn V (fun v => ψ v + ∑ i ∈ Finset.Icc 1 T, g i v) w) :
    (∑ t ∈ Finset.Icc 1 T, g t (z t - u) ≤
      ψ u - ψ (z 1) +
      ∑ t ∈ Finset.Icc 1 T,
        ((g t - g (t - 1)) (z t - (if t < T then z (t + 1) else w)) -
          lam / 2 * ‖z t - (if t < T then z (t + 1) else w)‖ ^ 2)) ∧
    (∑ t ∈ Finset.Icc 1 T, g t (z t - u) ≤
      ψ u - ψ (z 1) +
      ∑ t ∈ Finset.Icc 1 T, ‖g t - g (t - 1)‖ ^ 2 / (2 * lam)) := by sorry

end ModernOnlineLearning.SaddlePoint
