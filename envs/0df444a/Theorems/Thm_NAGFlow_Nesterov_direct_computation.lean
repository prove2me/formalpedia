-- Prove2me | Theorems.Thm_NAGFlow_Nesterov_direct_computation
-- name    : NAGFlow.Nesterov.direct_computation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:58.755276+00:00
-- url     : https://prove2.me/theorems/9b284d20-26ec-4edc-b63e-30150a9196d9
-- title:
--   Proof of Theorem 6.1, p. 24 — the identity for (γ_{k+1}/2)‖v_{k+1} − x*‖² − (γ_k/2)(1 − α_k)‖v_k − x*‖² along (96)
-- statement:
--   Let $V$ be a real Hilbert space and $\nabla f:V\to V$ a map. Let $\alpha_k>0$, $\gamma_k>0$, $\gamma_{k+1}>0$, and let $x_k,y_k,v_k,v_{k+1}\in V$ satisfy one step of the scheme (96). Then for every $x^*\in V$,
--   $$\begin{aligned}\frac{\gamma_{k+1}}{2}\|v_{k+1}-x^*\|^2-\frac{\gamma_k}{2}(1-\alpha_k)\|v_k-x^*\|^2 ={}& \alpha_k\Big(\langle\nabla f(y_k),x^*-y_k\rangle+\frac{\mu}{2}\|x^*-y_k\|^2\Big)\\ &+(1-\alpha_k)\Big(\langle\nabla f(y_k),x_k-y_k\rangle+\frac{\mu}{2}\|x_k-y_k\|^2\Big)\\ &+\frac{\alpha_k^2}{2\gamma_{k+1}}\|\nabla f(y_k)\|^2-\frac{\mu(1-\alpha_k)}{2\alpha_k\gamma_k}(\gamma_k+\mu\alpha_k)\|y_k-x_k\|^2.\end{aligned}$$
--
--   The identity is purely algebraic in the vector $\nabla f(y_k)$; it isolates the two first-order expressions that $\mu$-convexity of $f$ bounds, and is the core of the Lyapunov analysis of Nesterov's method.
--
--   **Formalization Note.** The statement is for one step of (96) and an arbitrary point $x^*$ (the paper uses a minimiser, but the identity does not depend on it). The positivity of $\alpha_k$, $\gamma_k$, $\gamma_{k+1}$ is added; it holds along every run of Algorithm 1. $\|\cdot\|_*$ is the norm of $V$ (Riesz).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 6.1, second display, p. 24

import Mathlib
import Definitions.Def_NAGFlow_Nesterov_Setting

namespace NAGFlow.Nesterov

/-- Proof of Theorem 6.1, second display, p. 24 (Luo & Chen, arXiv:1909.03145v4). For one step of the
scheme (96) with `α_k > 0`, `γ_k > 0`, `γ_{k+1} > 0`, and every point `x*`:
`(γ_{k+1}/2)‖v_{k+1} − x*‖² − (γ_k/2)(1 − α_k)‖v_k − x*‖²
 = α_k(⟨∇f(y_k), x* − y_k⟩ + (μ/2)‖x* − y_k‖²) + (1 − α_k)(⟨∇f(y_k), x_k − y_k⟩ + (μ/2)‖x_k − y_k‖²)
   + (α_k²/(2γ_{k+1}))‖∇f(y_k)‖² − (μ(1 − α_k)/(2α_kγ_k))(γ_k + μα_k)‖y_k − x_k‖²`. -/
theorem direct_computation {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradf : V → V) (μ αk γk γk1 : ℝ) (hα : 0 < αk) (hγ : 0 < γk) (hγ1 : 0 < γk1)
    (xk yk vk vk1 : V) (hstep : IsScheme96Step gradf μ αk γk γk1 xk yk vk vk1) (xstar : V) :
    γk1 / 2 * ‖vk1 - xstar‖ ^ 2 - γk / 2 * (1 - αk) * ‖vk - xstar‖ ^ 2 =
      αk * (inner ℝ (gradf yk) (xstar - yk) + μ / 2 * ‖xstar - yk‖ ^ 2)
        + (1 - αk) * (inner ℝ (gradf yk) (xk - yk) + μ / 2 * ‖xk - yk‖ ^ 2)
        + αk ^ 2 / (2 * γk1) * ‖gradf yk‖ ^ 2
        - μ * (1 - αk) / (2 * αk * γk) * (γk + μ * αk) * ‖yk - xk‖ ^ 2 := by sorry

end NAGFlow.Nesterov
