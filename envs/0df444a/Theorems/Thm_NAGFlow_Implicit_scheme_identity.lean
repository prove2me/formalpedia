-- Prove2me | Theorems.Thm_NAGFlow_Implicit_scheme_identity
-- name    : NAGFlow.Implicit.scheme_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:11.003551+00:00
-- url     : https://prove2.me/theorems/c5881e4a-7bec-4936-a3b5-d407cb665196
-- title:
--   Proof of Theorem 4.1, third display, p. 17 — by (72), γ_k(v_{k+1} − v_k, v_{k+1} − x*) = μα_k(…) − α_k⟨∇f(x_{k+1}), v_{k+1} − x*⟩
-- statement:
--   Let $V$ be a real Hilbert space, $\nabla f:V\to V$ any map, $x^*\in V$, $\mu\in\mathbb R$, $(x_k),(v_k)$ sequences in $V$ and $(\alpha_k),(\gamma_k)$ real sequences. Fix $k$ with $\alpha_k>0$ and $\gamma_k>0$, and suppose the second line of the implicit scheme (72) holds at step $k$:
--   $$\frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(x_{k+1}-v_{k+1})-\frac1{\gamma_k}\nabla f(x_{k+1}).$$
--   Then
--
--   $$\gamma_k\left(v_{k+1}-v_k,v_{k+1}-x^*\right)=\mu\alpha_k\left(x_{k+1}-v_{k+1},v_{k+1}-x^*\right)-\alpha_k\langle\nabla f(x_{k+1}),v_{k+1}-x^*\rangle .$$
--
--   The identity substitutes the scheme into the cross term of the Lyapunov difference.
--
--   **Formalization Note.** The hypothesis $\gamma_k>0$ is not written in the display; the page's (72) divides by $\gamma_k$, and along a run of (72)–(73) it follows from $\gamma_0>0$, $\mu\ge0$, $\alpha_k>0$ (Remark 4.1 records $0<\gamma_k$). Without it Lean's convention $1/0=0$ would change the meaning of (72). Inner product and duality pairing are both the real inner product (Riesz).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 4.1, third display ('By (72), it follows that'), p. 17; scheme (72), p. 16

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

namespace NAGFlow.Implicit

open scoped RealInnerProductSpace

/-- Proof of Theorem 4.1, third display, p. 17: if `α_k > 0`, `γ_k > 0` and the second line of
(72) holds at step `k`, then
`γ_k ⟪v_{k+1} - v_k, v_{k+1} - x*⟫
  = μ α_k ⟪x_{k+1} - v_{k+1}, v_{k+1} - x*⟫ - α_k ⟪∇f(x_{k+1}), v_{k+1} - x*⟫`. -/
theorem scheme_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (gradf : V → V) (xstar : V) (μ : ℝ) (α γ : ℕ → ℝ) (x v : ℕ → V)
    (k : ℕ) (hα : 0 < α k) (hγ : 0 < γ k)
    (hv : (1 / α k) • (v (k + 1) - v k)
      = (μ / γ k) • (x (k + 1) - v (k + 1)) - (1 / γ k) • gradf (x (k + 1))) :
    γ k * ⟪v (k + 1) - v k, v (k + 1) - xstar⟫
      = μ * α k * ⟪x (k + 1) - v (k + 1), v (k + 1) - xstar⟫
        - α k * ⟪gradf (x (k + 1)), v (k + 1) - xstar⟫ := by sorry

end NAGFlow.Implicit
