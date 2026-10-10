-- Prove2me | Theorems.Thm_NAGFlow_Implicit_diff_identity
-- name    : NAGFlow.Implicit.diff_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:54.972844+00:00
-- url     : https://prove2.me/theorems/922f7712-9d42-401c-abd7-8be309682a21
-- title:
--   Proof of Theorem 4.1, first display, p. 17 — the difference ℒ_{k+1} − ℒ_k under (73)
-- statement:
--   Let $V$ be a real Hilbert space, $f:V\to\mathbb R$, $x^*\in V$, $\mu\in\mathbb R$, and let $(x_k),(v_k)$ be sequences in $V$ and $(\alpha_k),(\gamma_k)$ real sequences, with $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}2\|v_k-x^*\|^2$ as in (74). Fix $k$ and suppose $\alpha_k>0$ and the parameter equation (73) holds at step $k$: $(\gamma_{k+1}-\gamma_k)/\alpha_k=\mu-\gamma_{k+1}$. Then
--
--   $$\begin{aligned}\mathcal L_{k+1}-\mathcal L_k&=f(x_{k+1})-f(x_k)+\frac{\gamma_{k+1}-\gamma_k}{2}\|v_{k+1}-x^*\|^2+\frac{\gamma_k}2\left(\|v_{k+1}-x^*\|^2-\|v_k-x^*\|^2\right)\\&=f(x_{k+1})-f(x_k)+\frac{\alpha_k}2(\mu-\gamma_{k+1})\|v_{k+1}-x^*\|^2+\gamma_k\left(v_{k+1}-v_k,\tfrac{v_{k+1}+v_k}2-x^*\right).\end{aligned}$$
--
--   This is the discrete counterpart of differentiating the Lyapunov function of the NAG flow, and is the first step of the proof that the implicit scheme contracts $\mathcal L_k$.
--
--   **Formalization Note.** No assumption on $f$ is needed. The inner product $(\cdot,\cdot)$ is the real inner product of `InnerProductSpace ℝ V`, and $(v_{k+1}+v_k)/2$ is written $\tfrac12\cdot(v_{k+1}+v_k)$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 4.1, first display (after (75)), p. 17

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

namespace NAGFlow.Implicit

open scoped RealInnerProductSpace

/-- Proof of Theorem 4.1, first display, p. 17: if `α_k > 0` and `γ` satisfies (73) at step `k`,
then for any `f`, `x*` and sequences `x, v`,
`ℒ_{k+1} - ℒ_k = f(x_{k+1}) - f(x_k) + (γ_{k+1} - γ_k)/2 ‖v_{k+1} - x*‖²
    + γ_k/2 (‖v_{k+1} - x*‖² - ‖v_k - x*‖²)
  = f(x_{k+1}) - f(x_k) + α_k/2 (μ - γ_{k+1}) ‖v_{k+1} - x*‖²
    + γ_k ⟪v_{k+1} - v_k, (v_{k+1} + v_k)/2 - x*⟫`. -/
theorem diff_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V → ℝ) (xstar : V) (μ : ℝ) (α γ : ℕ → ℝ) (x v : ℕ → V) (k : ℕ)
    (hα : 0 < α k) (hγ : (γ (k + 1) - γ k) / α k = μ - γ (k + 1)) :
    (lyap f xstar x v γ (k + 1) - lyap f xstar x v γ k
        = f (x (k + 1)) - f (x k) + (γ (k + 1) - γ k) / 2 * ‖v (k + 1) - xstar‖ ^ 2
          + γ k / 2 * (‖v (k + 1) - xstar‖ ^ 2 - ‖v k - xstar‖ ^ 2)) ∧
    (lyap f xstar x v γ (k + 1) - lyap f xstar x v γ k
        = f (x (k + 1)) - f (x k) + α k / 2 * (μ - γ (k + 1)) * ‖v (k + 1) - xstar‖ ^ 2
          + γ k * ⟪v (k + 1) - v k, (1 / 2 : ℝ) • (v (k + 1) + v k) - xstar⟫) := by sorry

end NAGFlow.Implicit
