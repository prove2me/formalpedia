-- Prove2me | Theorems.Thm_NAGFlow_Nesterov_v_formulas
-- name    : NAGFlow.Nesterov.v_formulas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:07.846142+00:00
-- url     : https://prove2.me/theorems/7fbbad5b-b58d-4a96-90ba-0b65cbb8efb6
-- title:
--   Proof of Theorem 6.1, p. 24 — from (96): v_k and v_{k+1} in terms of y_k, x_k and ∇f(y_k)
-- statement:
--   Let $V$ be a real Hilbert space and $\nabla f:V\to V$ a map. Let $\alpha_k>0$, $\gamma_k>0$, $\gamma_{k+1}>0$, and let $x_k,y_k,v_k,v_{k+1}\in V$ satisfy one step of the scheme (96):
--   $$\frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_k,\qquad \frac{y_k-x_k}{\alpha_k}=\frac{\gamma_k}{\gamma_{k+1}}(v_k-y_k),\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_{k+1}}(y_k-v_k)-\frac{1}{\gamma_{k+1}}\nabla f(y_k).$$
--   Then
--   $$v_k=y_k+\frac{\gamma_{k+1}}{\alpha_k\gamma_k}(y_k-x_k),\qquad v_{k+1}=y_k+\frac{1-\alpha_k}{\alpha_k}(y_k-x_k)-\frac{\alpha_k}{\gamma_{k+1}}\nabla f(y_k).$$
--
--   These expressions eliminate $v_k$ and $v_{k+1}$ in favour of the extrapolation point $y_k$, and are the input of the direct computation in the proof of Theorem 6.1.
--
--   **Formalization Note.** The statement is for one step of (96). The positivity of $\alpha_k$, $\gamma_k$, $\gamma_{k+1}$ is added; it holds along every run of Algorithm 1 (Theorem 6.1, Lemma B.1) and makes the divisions meaningful.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 6.1, first display, p. 24

import Mathlib
import Definitions.Def_NAGFlow_Nesterov_Setting

namespace NAGFlow.Nesterov

/-- Proof of Theorem 6.1, first display, p. 24 (Luo & Chen, arXiv:1909.03145v4). For one step of the
scheme (96) with `α_k > 0`, `γ_k > 0`, `γ_{k+1} > 0`:
`v_k = y_k + (γ_{k+1}/(α_kγ_k))(y_k − x_k)` and
`v_{k+1} = y_k + ((1 − α_k)/α_k)(y_k − x_k) − (α_k/γ_{k+1})∇f(y_k)`. -/
theorem v_formulas {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradf : V → V) (μ αk γk γk1 : ℝ) (hα : 0 < αk) (hγ : 0 < γk) (hγ1 : 0 < γk1)
    (xk yk vk vk1 : V) (hstep : IsScheme96Step gradf μ αk γk γk1 xk yk vk vk1) :
    vk = yk + (γk1 / (αk * γk)) • (yk - xk) ∧
      vk1 = yk + ((1 - αk) / αk) • (yk - xk) - (αk / γk1) • gradf yk := by sorry

end NAGFlow.Nesterov
