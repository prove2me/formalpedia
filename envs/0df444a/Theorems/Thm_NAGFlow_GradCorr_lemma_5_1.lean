-- Prove2me | Theorems.Thm_NAGFlow_GradCorr_lemma_5_1
-- name    : NAGFlow.GradCorr.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:42.426121+00:00
-- url     : https://prove2.me/theorems/e8f37785-8cc6-4811-90be-e5980c676c5b
-- title:
--   Lemma 5.1, p. 19 — one Gauss–Seidel step (80) with any α_k > 0 satisfies (81) and (82) for f ∈ S¹_μ
-- statement:
--   Let $V$ be a real Hilbert space, $f\in\mathcal S^1_\mu$ with $\mu\ge0$, and let $x^*$ be a global minimiser of $f$. Fix $(x_k,v_k)\in V^2$, $\gamma_k>0$ and a step size $\alpha_k>0$. Let $(x_{k+1},v_{k+1})$ satisfy the Gauss–Seidel step (80),
--   $$\frac{x_{k+1}-x_k}{\alpha_k}=v_k-x_{k+1},\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(x_{k+1}-v_{k+1})-\frac{1}{\gamma_k}\nabla f(x_{k+1}),$$
--   and let $\gamma_{k+1}$ satisfy $(\gamma_{k+1}-\gamma_k)/\alpha_k=\mu-\gamma_{k+1}$ (73). With $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}2\|v_k-x^*\|^2$ and $\mathcal L_{k+1}$ defined in the same way from $(x_{k+1},v_{k+1},\gamma_{k+1})$,
--   $$\mathcal L_{k+1}-\mathcal L_k\le-\alpha_k\mathcal L_{k+1}-\frac{\gamma_k}{2}\|v_{k+1}-v_k\|^2-\alpha_k\langle\nabla f(x_{k+1}),v_{k+1}-v_k\rangle\qquad(81)$$
--   and
--   $$\mathcal L_{k+1}-\mathcal L_k\le-\alpha_k\mathcal L_{k+1}+\frac{\alpha_k^2}{2\gamma_k}\|\nabla f(x_{k+1})\|^2.\qquad(82)$$
--
--   The estimate (82) leaves a positive gradient-norm term that prevents the contraction of Theorem 4.1 for the plain splitting. The corrected scheme (91) of §5.3 applies this lemma with $x_{k+1}$ replaced by $y_k$ and cancels that term with an extra gradient step.
--
--   **Formalization Note.** The lemma is stated for a single step, with $\gamma_k>0$ as a hypothesis (in a run of (73) it follows from $\gamma_0>0$); this is the form in which §5.3 applies it to the first two lines of (91). $\|\cdot\|_*$ is the norm of $V$ (Riesz). The hypothesis that $x^*$ minimises $f$ is the paper's standing assumption (p. 2).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Lemma 5.1 and Eqs. (80)–(82), p. 19

import Mathlib
import Definitions.Def_NAGFlow_GradCorr_Setting

namespace NAGFlow.GradCorr

/-- Lemma 5.1 (Luo & Chen, arXiv:1909.03145v4, p. 19), stated for one step of the Gauss–Seidel
splitting (80) together with one step of (73). Let `f ∈ S¹_μ` with `μ ≥ 0` and let `x*` be a global
minimiser of `f`. Given `(x_k, v_k)`, `γ_k > 0` and a step size `α_k > 0`, let `(x_{k+1}, v_{k+1})`
satisfy (80) and `γ_{k+1}` satisfy `(γ_{k+1} − γ_k)/α_k = μ − γ_{k+1}`. With
`ℒ_k = f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²` and `ℒ_{k+1}` likewise, (81) and (82) hold. -/
theorem lemma_5_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (αk γk γk1 : ℝ) (hα : 0 < αk) (hγ : 0 < γk)
    (hγk1 : (γk1 - γk) / αk = μ - γk1)
    (xk vk xk1 vk1 : V) (hstep : NAGFlow.PredCorr.IsGSStep gradf μ αk γk xk vk xk1 vk1) :
    NAGFlow.PredCorr.lyapPt f xstar xk1 vk1 γk1 - NAGFlow.PredCorr.lyapPt f xstar xk vk γk ≤
        -αk * NAGFlow.PredCorr.lyapPt f xstar xk1 vk1 γk1 - γk / 2 * ‖vk1 - vk‖ ^ 2
          - αk * inner ℝ (gradf xk1) (vk1 - vk) ∧
      NAGFlow.PredCorr.lyapPt f xstar xk1 vk1 γk1 - NAGFlow.PredCorr.lyapPt f xstar xk vk γk ≤
        -αk * NAGFlow.PredCorr.lyapPt f xstar xk1 vk1 γk1 + αk ^ 2 / (2 * γk) * ‖gradf xk1‖ ^ 2 := by sorry

end NAGFlow.GradCorr
