-- Prove2me | Theorems.Thm_NAGFlow_GradCorr_eq_93
-- name    : NAGFlow.GradCorr.eq_93
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:51.80876+00:00
-- url     : https://prove2.me/theorems/391181b1-60b1-4b26-a472-5fe85b8bb330
-- title:
--   (93), p. 22 — on a run of (91) + (73), ℒ̂_k − ℒ_k ≤ −α_kℒ̂_k + (α_k²/(2γ_k))‖∇f(y_k)‖²
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^1_\mu$ with $\mu\ge0$, and let $x^*$ be a global minimiser of $f$. Let $(\alpha_k,\gamma_k)$ satisfy (73) with $\gamma_0>0$ and step sizes $\alpha_k>0$, and let $(x_k,y_k,v_k)$ be a run of the corrected scheme (91) for some constant $L$. With $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2$ (74) and
--   $$\widehat{\mathcal L}_k=f(y_k)-f(x^*)+\frac{\gamma_{k+1}}{2}\|v_{k+1}-x^*\|^2\qquad(84),$$
--   for every $k$,
--   $$\widehat{\mathcal L}_k-\mathcal L_k\le-\alpha_k\widehat{\mathcal L}_k+\frac{\alpha_k^2}{2\gamma_k}\|\nabla f(y_k)\|^2.\qquad(93)$$
--
--   This is (82) of Lemma 5.1 for the first two lines of (91), which form a Gauss–Seidel step (80) with $y_k$ in place of $x_{k+1}$. It is the first step of the proof of Theorem 5.2.
--
--   **Formalization Note.** Only the first two lines of (91) and (73) are used; the correction step and the value of $L$ play no role, and only $f\in\mathcal S^1_\mu$ is assumed. No step-size rule is assumed. $\|\cdot\|_*$ is the norm of $V$ (Riesz).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 5.2, Eq. (93), p. 22; (84) p. 20

import Mathlib
import Definitions.Def_NAGFlow_GradCorr_Setting

namespace NAGFlow.GradCorr

/-- Inequality (93) in the proof of Theorem 5.2 (Luo & Chen, arXiv:1909.03145v4, p. 22). Let
`f ∈ S¹_μ`, `x*` a global minimiser of `f`, and `(x, y, v)` a run of the corrected scheme (91) with
parameters `(α, γ)` from (73) (`γ₀ > 0`, any step sizes `α_k > 0`). With
`ℒ̂_k = f(y_k) − f(x*) + (γ_{k+1}/2)‖v_{k+1} − x*‖²` (84), for every `k`
`ℒ̂_k − ℒ_k ≤ −α_kℒ̂_k + (α_k²/(2γ_k))‖∇f(y_k)‖²`. -/
theorem eq_93 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : NAGFlow.PredCorr.IsGammaRun μ α γ)
    (x y v : ℕ → V) (hrun : IsGCRun gradf μ L α γ x y v) (k : ℕ) :
    NAGFlow.PredCorr.lyapHat f xstar y v γ k - NAGFlow.PredCorr.lyap f xstar x v γ k ≤
      -α k * NAGFlow.PredCorr.lyapHat f xstar y v γ k + α k ^ 2 / (2 * γ k) * ‖gradf (y k)‖ ^ 2 := by sorry

end NAGFlow.GradCorr
