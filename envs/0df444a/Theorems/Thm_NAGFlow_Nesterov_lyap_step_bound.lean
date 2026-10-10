-- Prove2me | Theorems.Thm_NAGFlow_Nesterov_lyap_step_bound
-- name    : NAGFlow.Nesterov.lyap_step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:22.605338+00:00
-- url     : https://prove2.me/theorems/80875eb7-30bc-4842-bef3-8f093c48ff66
-- title:
--   Proof of Theorem 6.1, p. 25 — ℒ_{k+1} − (1 − α_k)ℒ_k ≤ f(x_{k+1}) − f(y_k) + (α_k²/(2γ_{k+1}))‖∇f(y_k)‖²
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, and $x^*$ a global minimiser of $f$. Let $(\alpha_k,\gamma_k,x_k,y_k,v_k)$ be a run of Algorithm 1 and $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2$ the Lyapunov function (74). Then for every $k$,
--   $$\mathcal L_{k+1}-(1-\alpha_k)\mathcal L_k\le f(x_{k+1})-f(y_k)+\frac{\alpha_k^2}{2\gamma_{k+1}}\|\nabla f(y_k)\|^2 .$$
--
--   Combined with the sufficient-decrease step (97) and the step rule $L\alpha_k^2=\gamma_{k+1}$, the right-hand side is nonpositive, which is the contraction (98) of Theorem 6.1.
--
--   **Formalization Note.** Stated along runs of Algorithm 1 under the hypotheses of Theorem 6.1. $\|\cdot\|_*$ is the norm of $V$ (Riesz). The minimiser $x^*$ is the paper's standing assumption (p. 2).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 6.1, second display, p. 25

import Mathlib
import Definitions.Def_NAGFlow_Nesterov_Setting

namespace NAGFlow.Nesterov

/-- Proof of Theorem 6.1, second display of p. 25 (Luo & Chen, arXiv:1909.03145v4). Let
`f ∈ S^{1,1}_{μ,L}` with `0 ≤ μ ≤ L < ∞`, let `x*` be a global minimiser of `f`, and let
`(α, γ, x, y, v)` be a run of Algorithm 1. With `ℒ_k` the Lyapunov function (74), for every `k`,
`ℒ_{k+1} − (1 − α_k)ℒ_k ≤ f(x_{k+1}) − f(y_k) + (α_k²/(2γ_{k+1}))‖∇f(y_k)‖²`. -/
theorem lyap_step_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ z, f xstar ≤ f z)
    (α γ : ℕ → ℝ) (x y v : ℕ → V) (hrun : IsNAGRun f gradf μ L α γ x y v) (k : ℕ) :
    lyap f xstar x v γ (k + 1) - (1 - α k) * lyap f xstar x v γ k ≤
      f (x (k + 1)) - f (y k) + α k ^ 2 / (2 * γ (k + 1)) * ‖gradf (y k)‖ ^ 2 := by sorry

end NAGFlow.Nesterov
