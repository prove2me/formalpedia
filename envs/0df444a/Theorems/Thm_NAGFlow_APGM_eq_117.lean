-- Prove2me | Theorems.Thm_NAGFlow_APGM_eq_117
-- name    : NAGFlow.APGM.eq_117
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:48.665445+00:00
-- url     : https://prove2.me/theorems/1f1fc065-2f66-42dc-9bbf-c611c64361ed
-- title:
--   (117), proof of Theorem 7.2, p. 31 — ℒ̂_k − ℒ_k ≤ −α_kℒ̂_k + (1 + α_k)(f(y_k) − f(x_{k+1})) + (α_k²/(2γ_k) − (1 + α_k)/(2L))‖G_f(y_k)‖²
-- statement:
--   Let $V$ be a real Hilbert space, $f=h+g$ with $h\in\mathcal S^{1,1}_{\mu,L}$ ($0\le\mu\le L<\infty$) and $g:V\to\mathbb R\cup\{+\infty\}$ proper, closed and convex, and let $x^*\in\operatorname{dom}g$ minimise $f$. Let $(x_k,y_k,v_k,\gamma_k)$ be a run of the semi-implicit scheme (115) with $\gamma_0>0$ and arbitrary step sizes $\alpha_k>0$, started at $x_0\in\operatorname{dom}g$. With
--   $$\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}2\|v_k-x^*\|^2,\qquad \widehat{\mathcal L}_k=f(y_k)-f(x^*)+\frac{\gamma_{k+1}}2\|v_{k+1}-x^*\|^2\quad(84),$$
--   and $\mathcal G_f(y_k)=L(y_k-x_{k+1})$, for every $k$
--   $$\widehat{\mathcal L}_k-\mathcal L_k\le-\alpha_k\widehat{\mathcal L}_k+(1+\alpha_k)\big(f(y_k)-f(x_{k+1})\big)+\frac{\alpha_k^2}{2\gamma_k}\|\mathcal G_f(y_k)\|^2-\frac{1+\alpha_k}{2L}\|\mathcal G_f(y_k)\|^2.\qquad(117)$$
--
--   With the step size $L\alpha_k^2=\gamma_k(1+\alpha_k)$ the last two terms cancel, and the identity $f(y_k)-f(x_{k+1})=\widehat{\mathcal L}_k-\mathcal L_{k+1}$ turns (117) into the contraction (116).
--
--   **Formalization Note.** No step-size rule is assumed: (117) holds for every $\alpha_k>0$. The point $y_k$ may lie outside $\operatorname{dom}g$; there the page's $f(y_k)$ is $+\infty$. In the encoding $f(y_k)$ is a real number, and it enters both sides with total coefficient $1$, so the inequality does not depend on the value $g$ takes at $y_k$; no hypothesis $y_k\in\operatorname{dom}g$ is added. The hypothesis $x_0\in\operatorname{dom}g$ is added: without it the page's $\mathcal L_0$ is $+\infty$ and the case $k=0$ is void ($x_k\in\operatorname{dom}g$ for $k\ge1$ follows from the prox step). $x^*$ minimises $f$ over $\operatorname{dom}g$ (argmin $f$ nonempty, p. 2).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 7.2, (117), p. 31; (84), p. 20; (115), p. 30

import Mathlib
import Definitions.Def_NAGFlow_APGM_Setting

namespace NAGFlow.APGM

/-- Inequality (117) (Luo & Chen, arXiv:1909.03145v4, proof of Theorem 7.2, p. 31). Let
`h ∈ S^{1,1}_{μ,L}` with `0 ≤ μ ≤ L < ∞`, `g : V → ℝ ∪ {+∞}` proper, closed and convex (encoded by
`(g, D)`), `f = h + g`, and `x* ∈ dom g` a minimiser of `f`. Let `(x, y, v)` be a run of the
semi-implicit scheme (115) with `γ₀ > 0` and any step sizes `α_k > 0`, started at `x₀ ∈ dom g`. With
`ℒ_k = f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²`, `ℒ̂_k = f(y_k) − f(x*) + (γ_{k+1}/2)‖v_{k+1} − x*‖²` (84)
and `G_f(y_k) = L(y_k − x_{k+1})`, for every `k`
`ℒ̂_k − ℒ_k ≤ −α_kℒ̂_k + (1 + α_k)(f(y_k) − f(x_{k+1})) + (α_k²/(2γ_k))‖G_f(y_k)‖² − ((1 + α_k)/(2L))‖G_f(y_k)‖²`. -/
theorem eq_117 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D)
    (xstar : V) (hxstar : xstar ∈ D) (hmin : ∀ z ∈ D, (h + g) xstar ≤ (h + g) z)
    (α γ : ℕ → ℝ) (x y v : ℕ → V) (hrun : IsSemiImplicitRun gradh g D μ L α γ x y v)
    (hx0 : x 0 ∈ D) (k : ℕ) :
    NAGFlow.PredCorr.lyapHat (h + g) xstar y v γ k - NAGFlow.PredCorr.lyap (h + g) xstar x v γ k ≤
      -α k * NAGFlow.PredCorr.lyapHat (h + g) xstar y v γ k + (1 + α k) * ((h + g) (y k) - (h + g) (x (k + 1)))
        + α k ^ 2 / (2 * γ k) * ‖gradMap (1 / L) (y k) (x (k + 1))‖ ^ 2
        - (1 + α k) / (2 * L) * ‖gradMap (1 / L) (y k) (x (k + 1))‖ ^ 2 := by sorry

end NAGFlow.APGM
