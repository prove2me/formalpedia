-- Prove2me | Theorems.Thm_NAGFlow_GradCorr_plugged_bound
-- name    : NAGFlow.GradCorr.plugged_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:34.610094+00:00
-- url     : https://prove2.me/theorems/e79f1475-19d2-458f-a6c7-d9b8423a8cfd
-- title:
--   §5.3, p. 22 — on a run of (91) + (73), ℒ_{k+1} − ℒ_k ≤ −α_kℒ_{k+1} + (Lα_k² − γ_k(1 + α_k))‖∇f(y_k)‖²/(2Lγ_k)
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, and let $x^*$ be a global minimiser of $f$. Let $(\alpha_k,\gamma_k)$ satisfy (73) with $\gamma_0>0$ and arbitrary step sizes $\alpha_k>0$, and let $(x_k,y_k,v_k)$ be a run of the corrected scheme (91). With $\mathcal L_k$ of (74), for every $k$,
--   $$\mathcal L_{k+1}-\mathcal L_k\le-\alpha_k\mathcal L_{k+1}+\frac{1}{2L\gamma_k}\bigl(L\alpha_k^2-\gamma_k(1+\alpha_k)\bigr)\|\nabla f(y_k)\|^2.$$
--
--   The bound holds for every choice of step sizes. Its last term vanishes exactly when $L\alpha_k^2=\gamma_k(1+\alpha_k)$, which is the step-size rule of Theorem 5.2, and the contraction (92) follows.
--
--   **Formalization Note.** No step-size rule is assumed here. $\|\cdot\|_*$ is the norm of $V$ (Riesz).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 5.2, display "Plugging this into (93) gives", p. 22

import Mathlib
import Definitions.Def_NAGFlow_GradCorr_Setting

namespace NAGFlow.GradCorr

/-- The display "Plugging this into (93) gives" in the proof of Theorem 5.2 (Luo & Chen,
arXiv:1909.03145v4, p. 22). Let `f ∈ S^{1,1}_{μ,L}` with `0 ≤ μ ≤ L < ∞`, `x*` a global minimiser of
`f`, and `(x, y, v)` a run of the corrected scheme (91) with parameters `(α, γ)` from (73) (any step
sizes `α_k > 0`, no step rule). Then for every `k`
`ℒ_{k+1} − ℒ_k ≤ −α_kℒ_{k+1} + (1/(2Lγ_k))(Lα_k² − γ_k(1 + α_k))‖∇f(y_k)‖²`. -/
theorem plugged_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : NAGFlow.PredCorr.IsGammaRun μ α γ)
    (x y v : ℕ → V) (hrun : IsGCRun gradf μ L α γ x y v) (k : ℕ) :
    NAGFlow.PredCorr.lyap f xstar x v γ (k + 1) - NAGFlow.PredCorr.lyap f xstar x v γ k ≤
      -α k * NAGFlow.PredCorr.lyap f xstar x v γ (k + 1) +
        1 / (2 * L * γ k) * (L * α k ^ 2 - γ k * (1 + α k)) * ‖gradf (y k)‖ ^ 2 := by sorry

end NAGFlow.GradCorr
