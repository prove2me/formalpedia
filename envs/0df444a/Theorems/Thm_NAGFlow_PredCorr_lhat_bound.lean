-- Prove2me | Theorems.Thm_NAGFlow_PredCorr_lhat_bound
-- name    : NAGFlow.PredCorr.lhat_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:12.691248+00:00
-- url     : https://prove2.me/theorems/350890ff-d600-46cb-8db0-3a087fa1a770
-- title:
--   §5.2, p. 20 — for the predictor–corrector scheme, ℒ̂_k ≤ ℒ_k/(1 + α_k) − γ_k‖v_{k+1} − v_k‖²/(2(1 + α_k)) − α_k⟨∇f(y_k), v_{k+1} − v_k⟩/(1 + α_k)
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^1_\mu$, $x^*$ a global minimiser of $f$, $(\alpha_k,\gamma_k)$ satisfying (73) with $\gamma_0>0$ and $\alpha_k>0$, and $(x_k,y_k,v_k)$ a run of the predictor–corrector scheme (83). Put
--   $$\widehat{\mathcal L}_k=f(y_k)-f(x^*)+\frac{\gamma_{k+1}}{2}\|v_{k+1}-x^*\|^2.\qquad(84)$$
--   Then for every $k$,
--   $$\widehat{\mathcal L}_k-\mathcal L_k\le-\alpha_k\widehat{\mathcal L}_k-\frac{\gamma_k}{2}\|v_{k+1}-v_k\|^2-\alpha_k\langle\nabla f(y_k),v_{k+1}-v_k\rangle,$$
--   and consequently
--   $$\widehat{\mathcal L}_k\le\frac{\mathcal L_k}{1+\alpha_k}-\frac{\gamma_k}{2(1+\alpha_k)}\|v_{k+1}-v_k\|^2-\frac{\alpha_k}{1+\alpha_k}\langle\nabla f(y_k),v_{k+1}-v_k\rangle .$$
--
--   This is the predictor half of the analysis of (83): the first two lines of (83) are a Gauss–Seidel step (80) with $x_{k+1}$ replaced by $y_k$.
--
--   **Formalization Note.** $\mathcal L_k$ is (74). Only $f\in\mathcal S^1_\mu$ is assumed, as on the page; the Lipschitz bound enters only in the corrector step.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §5.2, displays after (83) and after (84), and (84), p. 20

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.PredCorr

/-- The bound on ℒ̂_k in §5.2 (Luo & Chen, arXiv:1909.03145v4, displays after (83) and after (84),
p. 20). Let `f ∈ S¹_μ`, `x*` a global minimiser of `f`, and `(x, y, v)` a run of the
predictor–corrector scheme (83) with parameters `(α, γ)` from (73). With
`ℒ̂_k = f(y_k) − f(x*) + (γ_{k+1}/2)‖v_{k+1} − x*‖²` (84), for every `k`
`ℒ̂_k − ℒ_k ≤ −α_kℒ̂_k − (γ_k/2)‖v_{k+1} − v_k‖² − α_k⟨∇f(y_k), v_{k+1} − v_k⟩` and therefore
`ℒ̂_k ≤ ℒ_k/(1 + α_k) − γ_k/(2(1 + α_k))‖v_{k+1} − v_k‖² − α_k/(1 + α_k)⟨∇f(y_k), v_{k+1} − v_k⟩`. -/
theorem lhat_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ : ℝ) (hf : IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : IsGammaRun μ α γ)
    (x y v : ℕ → V) (hrun : IsPCRun gradf μ α γ x y v) (k : ℕ) :
    lyapHat f xstar y v γ k - lyap f xstar x v γ k ≤
        -α k * lyapHat f xstar y v γ k - γ k / 2 * ‖v (k + 1) - v k‖ ^ 2
          - α k * inner ℝ (gradf (y k)) (v (k + 1) - v k) ∧
      lyapHat f xstar y v γ k ≤
        lyap f xstar x v γ k / (1 + α k) - γ k / (2 * (1 + α k)) * ‖v (k + 1) - v k‖ ^ 2
          - α k / (1 + α k) * inner ℝ (gradf (y k)) (v (k + 1) - v k) := by sorry

end NAGFlow.PredCorr
