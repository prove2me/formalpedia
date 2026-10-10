-- Prove2me | Theorems.Thm_NAGFlow_GradCorr_theorem_5_2
-- name    : NAGFlow.GradCorr.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:01.181378+00:00
-- url     : https://prove2.me/theorems/b0b8ed23-95a6-480c-b620-5ad2694b36a9
-- title:
--   Theorem 5.2, p. 22 — with Lα_k² = γ_k(1 + α_k), the gradient-corrected scheme (91) has ℒ_{k+1} ≤ ℒ_k/(1 + α_k), (87) and (88)
-- statement:
--   Let $V$ be a real Hilbert space and $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, and let $x^*$ be a global minimiser of $f$. Let $(\alpha_k,\gamma_k)$ satisfy the parameter equation (73),
--   $$\frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_{k+1},\qquad\gamma_0>0,\ \alpha_k>0,$$
--   with the step sizes chosen by $L\alpha_k^2=\gamma_k(1+\alpha_k)$, and let $(x_k,y_k,v_k)$ be a run of the corrected scheme (91),
--   $$\frac{y_k-x_k}{\alpha_k}=v_k-y_k,\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(y_k-v_{k+1})-\frac{1}{\gamma_k}\nabla f(y_k),\qquad x_{k+1}-y_k=-\frac{1}{L}\nabla f(y_k).$$
--   Let $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2$ (74). Then
--
--   1. for every $k\in\mathbb N$,
--   $$\mathcal L_{k+1}\le\frac{\mathcal L_k}{1+\alpha_k};\qquad(92)$$
--   2. for every $k\ge0$,
--   $$\mathcal L_k\le\mathcal L_0\times\min\left\{\frac{4L}{(\sqrt{\gamma_0}\,k+2\sqrt L)^2},\ \left(1+\sqrt{\frac{\min\{\gamma_0,\mu\}}{L}}\right)^{-k}\right\};\qquad(87)$$
--   3. for every $k\ge1$,
--   $$\mathcal L_k\le C_{\gamma_0,L}\times\min\left\{\frac{4}{k^2},\ \left(1+\sqrt{\frac{\min\{\gamma_0,\mu\}}{L}}\right)^{1-k}\right\},\qquad(88)$$
--   where
--   $$C_{\gamma_0,L}=\frac{L}{\gamma_0}\bigl(f(x_0)-f(x^*)\bigr)+\frac{L}{2}\|v_0-x^*\|^2.\qquad(89)$$
--
--   The corrected scheme evaluates the gradient once per step, at $y_k$, and attains the same accelerated rates as the predictor–corrector scheme of Theorem 5.1: $O(1/k^2)$ for convex $f$ and the linear rate $(1+\sqrt{\min\{\gamma_0,\mu\}/L})^{-k}$ for strongly convex $f$, in one statement covering $\mu=0$ and $\mu>0$.
--
--   **Formalization Note.** $V$ is a real Hilbert space, and the dual norm is its norm (Riesz). The gradient is an explicit map with `HasGradientAt` at every point. The scheme and (73) are hypotheses on given sequences; $\alpha_k$ is any positive sequence satisfying $L\alpha_k^2=\gamma_k(1+\alpha_k)$, not a formula. The positivity $\gamma_0>0$ and $\alpha_k>0$ are those of (73) and of the scheme; $0<L$ is part of the class. The paper states (87) and (88) by reference ("both the two estimates (87) and (88) hold true here"); they are written out in full, with the constants of p. 21. The negative and $1-k$ powers are integer powers of a number $\ge1$. When $\mu=0$ the second entry of each minimum equals $1$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Theorem 5.2 and Eq. (92), p. 22; (87)–(89) p. 21; scheme (91) p. 22; (73)–(74) p. 16

import Mathlib
import Definitions.Def_NAGFlow_GradCorr_Setting

namespace NAGFlow.GradCorr

/-- Theorem 5.2 (Luo & Chen, arXiv:1909.03145v4, p. 22). Let `f ∈ S^{1,1}_{μ,L}` with
`0 ≤ μ ≤ L < ∞`, let `x*` be a global minimiser of `f`, and let `(x, y, v)` be a run of the corrected
scheme (91) together with (73) (`γ₀ > 0`, `α_k > 0`), with step sizes chosen by
`Lα_k² = γ_k(1 + α_k)`. Then, with `ℒ_k` the Lyapunov function (74):
(92) `ℒ_{k+1} ≤ ℒ_k/(1 + α_k)` for every `k ∈ ℕ`;
(87) `ℒ_k ≤ ℒ₀ · min{4L/(√γ₀ k + 2√L)², (1 + √(min{γ₀, μ}/L))^{−k}}` for every `k ≥ 0`;
(88) `ℒ_k ≤ C_{γ₀,L} · min{4/k², (1 + √(min{γ₀, μ}/L))^{1−k}}` for every `k ≥ 1`, where
(89) `C_{γ₀,L} = (L/γ₀)(f(x₀) − f(x*)) + (L/2)‖v₀ − x*‖²`. -/
theorem theorem_5_2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : NAGFlow.PredCorr.IsGammaRun μ α γ)
    (hstep : ∀ k, L * α k ^ 2 = γ k * (1 + α k))
    (x y v : ℕ → V) (hrun : IsGCRun gradf μ L α γ x y v) :
    (∀ k : ℕ, NAGFlow.PredCorr.lyap f xstar x v γ (k + 1) ≤ NAGFlow.PredCorr.lyap f xstar x v γ k / (1 + α k)) ∧
      (∀ k : ℕ, NAGFlow.PredCorr.lyap f xstar x v γ k ≤
        NAGFlow.PredCorr.lyap f xstar x v γ 0 *
          min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
            ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ)))) ∧
      (∀ k : ℕ, 1 ≤ k → NAGFlow.PredCorr.lyap f xstar x v γ k ≤
        (L / γ 0 * (f (x 0) - f xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2) *
          min (4 / (k : ℝ) ^ 2) ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (1 - (k : ℤ)))) := by sorry

end NAGFlow.GradCorr
