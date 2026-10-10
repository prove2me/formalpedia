-- Prove2me | Theorems.Thm_NAGFlow_PredCorr_eq_85
-- name    : NAGFlow.PredCorr.eq_85
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:14.810919+00:00
-- url     : https://prove2.me/theorems/ecf7dc91-9d68-4f27-a008-e6f2158d12c6
-- title:
--   (85), p. 21 — for f ∈ S^{1,1}_{μ,L}, ℒ_{k+1} ≤ ℒ_k/(1 + α_k) + (Lα_k²/(2(1 + α_k)²) − γ_k/(2(1 + α_k)))‖v_{k+1} − v_k‖²
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, $x^*$ a global minimiser of $f$, $(\alpha_k,\gamma_k)$ satisfying (73) with $\gamma_0>0$ and arbitrary step sizes $\alpha_k>0$, and $(x_k,y_k,v_k)$ a run of the predictor–corrector scheme (83). Then for every $k$,
--   $$\mathcal L_{k+1}\le\frac{\mathcal L_k}{1+\alpha_k}+\left(\frac{L\alpha_k^2}{2(1+\alpha_k)^2}-\frac{\gamma_k}{2(1+\alpha_k)}\right)\|v_{k+1}-v_k\|^2,\qquad(85)$$
--   where $\mathcal L_k$ is the Lyapunov function (74).
--
--   The second term vanishes exactly when $L\alpha_k^2=\gamma_k(1+\alpha_k)$, which is the step-size rule of Theorem 5.1.
--
--   **Formalization Note.** No step-size relation is assumed here; $\alpha_k>0$ is the only constraint, as in the page's derivation.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (85), p. 21 (derivation on p. 20)

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.PredCorr

/-- Inequality (85) (Luo & Chen, arXiv:1909.03145v4, p. 21). Let `f ∈ S^{1,1}_{μ,L}` with
`0 ≤ μ ≤ L < ∞`, `x*` a global minimiser of `f`, and `(x, y, v)` a run of the predictor–corrector
scheme (83) with parameters `(α, γ)` from (73) (any step sizes `α_k > 0`). Then for every `k`
`ℒ_{k+1} ≤ ℒ_k/(1 + α_k) + (Lα_k²/(2(1 + α_k)²) − γ_k/(2(1 + α_k)))‖v_{k+1} − v_k‖²`. -/
theorem eq_85 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : IsGammaRun μ α γ)
    (x y v : ℕ → V) (hrun : IsPCRun gradf μ α γ x y v) (k : ℕ) :
    lyap f xstar x v γ (k + 1) ≤
      lyap f xstar x v γ k / (1 + α k) +
        (L * α k ^ 2 / (2 * (1 + α k) ^ 2) - γ k / (2 * (1 + α k))) * ‖v (k + 1) - v k‖ ^ 2 := by sorry

end NAGFlow.PredCorr
