-- Prove2me | Theorems.Thm_NAGFlow_Nesterov_mu_convexity_bound
-- name    : NAGFlow.Nesterov.mu_convexity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:19.114062+00:00
-- url     : https://prove2.me/theorems/8889e036-64ec-4b40-8e94-cdcd7dae8cb2
-- title:
--   Proof of Theorem 6.1, p. 25 — dropping −‖y_k − x_k‖² and μ-convexity give the bound on (γ_{k+1}/2)‖v_{k+1} − x*‖² − (γ_k/2)(1 − α_k)‖v_k − x*‖²
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, and $x^*$ a global minimiser of $f$. Let $(\alpha_k,\gamma_k,x_k,y_k,v_k)$ be a run of Algorithm 1 (Nesterov's accelerated gradient method). Then for every $k$,
--   $$\frac{\gamma_{k+1}}{2}\|v_{k+1}-x^*\|^2-\frac{\gamma_k}{2}(1-\alpha_k)\|v_k-x^*\|^2\le\alpha_k\big(f(x^*)-f(y_k)\big)+(1-\alpha_k)\big(f(x_k)-f(y_k)\big)+\frac{\alpha_k^2}{2\gamma_{k+1}}\|\nabla f(y_k)\|^2 .$$
--
--   This is the step of the proof of Theorem 6.1 where the convexity of $f$ enters.
--
--   **Formalization Note.** Stated along runs of Algorithm 1 under the hypotheses of Theorem 6.1, so that $0<\alpha_k\le1$ and $\gamma_k>0$ (which the paper uses when it drops the term in $\|y_k-x_k\|^2$) are consequences of the run rather than added assumptions. $\|\cdot\|_*$ is the norm of $V$ (Riesz). The minimiser $x^*$ is the paper's standing assumption (p. 2).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 6.1, first display, p. 25

import Mathlib
import Definitions.Def_NAGFlow_Nesterov_Setting

namespace NAGFlow.Nesterov

/-- Proof of Theorem 6.1, first display of p. 25 (Luo & Chen, arXiv:1909.03145v4). Let
`f ∈ S^{1,1}_{μ,L}` with `0 ≤ μ ≤ L < ∞`, let `x*` be a global minimiser of `f`, and let
`(α, γ, x, y, v)` be a run of Algorithm 1. Then for every `k`,
`(γ_{k+1}/2)‖v_{k+1} − x*‖² − (γ_k/2)(1 − α_k)‖v_k − x*‖²
 ≤ α_k(f(x*) − f(y_k)) + (1 − α_k)(f(x_k) − f(y_k)) + (α_k²/(2γ_{k+1}))‖∇f(y_k)‖²`. -/
theorem mu_convexity_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ z, f xstar ≤ f z)
    (α γ : ℕ → ℝ) (x y v : ℕ → V) (hrun : IsNAGRun f gradf μ L α γ x y v) (k : ℕ) :
    γ (k + 1) / 2 * ‖v (k + 1) - xstar‖ ^ 2 - γ k / 2 * (1 - α k) * ‖v k - xstar‖ ^ 2 ≤
      α k * (f xstar - f (y k)) + (1 - α k) * (f (x k) - f (y k))
        + α k ^ 2 / (2 * γ (k + 1)) * ‖gradf (y k)‖ ^ 2 := by sorry

end NAGFlow.Nesterov
