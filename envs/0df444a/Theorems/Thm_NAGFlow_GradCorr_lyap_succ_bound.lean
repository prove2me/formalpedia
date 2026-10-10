-- Prove2me | Theorems.Thm_NAGFlow_GradCorr_lyap_succ_bound
-- name    : NAGFlow.GradCorr.lyap_succ_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:48.121669+00:00
-- url     : https://prove2.me/theorems/91d1bff2-f071-42e5-8fb4-56b28a49881d
-- title:
--   §5.3, display after (94), p. 22 — on a run of (91) + (73), ℒ_{k+1} ≤ ℒ̂_k − ‖∇f(y_k)‖²/(2L)
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, and let $x^*$ be a global minimiser of $f$. Let $(\alpha_k,\gamma_k)$ satisfy (73) with $\gamma_0>0$ and $\alpha_k>0$, and let $(x_k,y_k,v_k)$ be a run of the corrected scheme (91). With $\mathcal L_k$ of (74) and $\widehat{\mathcal L}_k$ of (84), for every $k$,
--   $$\mathcal L_{k+1}\le\widehat{\mathcal L}_k-\frac{1}{2L}\|\nabla f(y_k)\|^2.$$
--
--   Since $\mathcal L_{k+1}$ and $\widehat{\mathcal L}_k$ share $\gamma_{k+1}$ and $v_{k+1}$, this is the gradient descent inequality (94) for the correction step of (91).
--
--   **Formalization Note.** No step-size rule is assumed. $\|\cdot\|_*$ is the norm of $V$ (Riesz).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 5.2, display after (94), p. 22

import Mathlib
import Definitions.Def_NAGFlow_GradCorr_Setting

namespace NAGFlow.GradCorr

/-- The display after (94) (Luo & Chen, arXiv:1909.03145v4, p. 22). Let `f ∈ S^{1,1}_{μ,L}` with
`0 ≤ μ ≤ L < ∞`, `x*` a global minimiser of `f`, and `(x, y, v)` a run of the corrected scheme (91)
with parameters `(α, γ)` from (73). Then for every `k`
`ℒ_{k+1} ≤ ℒ̂_k − (1/(2L))‖∇f(y_k)‖²`, with `ℒ_k` of (74) and `ℒ̂_k` of (84). -/
theorem lyap_succ_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : NAGFlow.PredCorr.IsGammaRun μ α γ)
    (x y v : ℕ → V) (hrun : IsGCRun gradf μ L α γ x y v) (k : ℕ) :
    NAGFlow.PredCorr.lyap f xstar x v γ (k + 1) ≤
      NAGFlow.PredCorr.lyapHat f xstar y v γ k - 1 / (2 * L) * ‖gradf (y k)‖ ^ 2 := by sorry

end NAGFlow.GradCorr
