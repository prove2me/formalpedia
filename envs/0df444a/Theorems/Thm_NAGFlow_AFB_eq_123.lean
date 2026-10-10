-- Prove2me | Theorems.Thm_NAGFlow_AFB_eq_123
-- name    : NAGFlow.AFB.eq_123
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:58.123662+00:00
-- url     : https://prove2.me/theorems/2f2fd23f-b4aa-41b1-a2b8-d5d03c336bc9
-- title:
--   (123), p. 34 — ℒ_{k+1} − ℒ_k ≤ −α_kℒ_{k+1} + (1 + α_k)(h(x_{k+1}) − h(y_k)) − α_k⟨∇h(y_k), v_{k+1} − v_k⟩ − … − α_k(g(v_{k+1}) − g(x_{k+1}))
-- statement:
--   Let $V$ be a real Hilbert space, let $(Q,h,g)$ be an instance of the composite problem (104) with constants $0\le\mu\le L$, let $x^*$ minimise $f=h+g$ over $Q$, and let $(x_k,y_k,w_k,v_k)$ with parameters $(\alpha_k,\gamma_k)$ be a run of Algorithm 4 (Semi-AFB). With $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2$, for every $k$,
--   $$\begin{aligned}\mathcal L_{k+1}-\mathcal L_k\ \le\ &-\alpha_k\mathcal L_{k+1}+(1+\alpha_k)\bigl(h(x_{k+1})-h(y_k)\bigr)-\alpha_k\langle\nabla h(y_k),v_{k+1}-v_k\rangle\\&-\frac{\gamma_k}{2}\|v_{k+1}-v_k\|^2+g(x_{k+1})-g(x_k)-\alpha_k\bigl(g(v_{k+1})-g(x_{k+1})\bigr).\end{aligned}\qquad(123)$$
--
--   This is the key one-step estimate of the proof of Theorem 7.3: once the $h$-terms and the $g$-terms on the right are shown to be nonpositive, it gives the contraction $\mathcal L_{k+1}\le\mathcal L_k/(1+\alpha_k)$.
--
--   **Formalization Note.** No subgradient $p_{k+1}$ and no variational inequality is assumed: the statement is about every run of Algorithm 4, where $v_{k+1}$ is a genuine minimiser of the step-5 function over $Q\cap\operatorname{dom}g$. The values $g(x_k)$, $g(x_{k+1})$ are the real numbers of the Lean encoding of $g$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 7.3, (123), p. 34

import Mathlib
import Definitions.Def_NAGFlow_AFB_Setting

namespace NAGFlow.AFB

/-- (123), p. 34 (Luo & Chen, arXiv:1909.03145v4). For a run of Algorithm 4 for (104), a minimiser
`x*` of `f = h + g` over `Q`, and `ℒ_k = f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²`, for every `k`,
`ℒ_{k+1} − ℒ_k ≤ −α_kℒ_{k+1} + (1 + α_k)(h(x_{k+1}) − h(y_k)) − α_k⟪∇h(y_k), v_{k+1} − v_k⟫
  − (γ_k/2)‖v_{k+1} − v_k‖² + g(x_{k+1}) − g(x_k) − α_k(g(v_{k+1}) − g(x_{k+1}))`. -/
theorem eq_123 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ)
    (hprob : IsAFBProblem h gradh g D Q μ L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAFBRun gradh g D Q μ L α γ x y w v)
    (xstar : V) (hxstar : IsMinimizer h g D Q xstar) :
    ∀ k : ℕ, lyap h g xstar x v γ (k + 1) - lyap h g xstar x v γ k ≤
      -α k * lyap h g xstar x v γ (k + 1) + (1 + α k) * (h (x (k + 1)) - h (y k)) -
        α k * inner ℝ (gradh (y k)) (v (k + 1) - v k) -
        γ k / 2 * ‖v (k + 1) - v k‖ ^ 2 + g (x (k + 1)) - g (x k) -
        α k * (g (v (k + 1)) - g (x (k + 1))) := by sorry

end NAGFlow.AFB
