-- Prove2me | Theorems.Thm_NAGFlow_Implicit_gradient_split
-- name    : NAGFlow.Implicit.gradient_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:03.629116+00:00
-- url     : https://prove2.me/theorems/dcb9c12f-39ef-4d16-a886-f1dc2efd2913
-- title:
--   Proof of Theorem 4.1, fifth display, p. 17 — the gradient term split by the first line of (72)
-- statement:
--   Let $V$ be a real Hilbert space, $\nabla f:V\to V$ any map, $x^*\in V$, $(x_k),(v_k)$ sequences in $V$ and $(\alpha_k)$ a real sequence. Fix $k$ with $\alpha_k>0$ and suppose the first line of the implicit scheme (72) holds at step $k$:
--   $$\frac{x_{k+1}-x_k}{\alpha_k}=v_{k+1}-x_{k+1}.$$
--   Then, writing $v_{k+1}-x^*=(v_{k+1}-x_{k+1})+(x_{k+1}-x^*)$,
--
--   $$-\alpha_k\langle\nabla f(x_{k+1}),v_{k+1}-x^*\rangle=-\langle\nabla f(x_{k+1}),x_{k+1}-x_k\rangle-\alpha_k\langle\nabla f(x_{k+1}),x_{k+1}-x^*\rangle .$$
--
--   The two terms on the right are the ones the $\mu$-convexity inequality (2) bounds, at the pairs $(x_k,x_{k+1})$ and $(x^*,x_{k+1})$.
--
--   **Formalization Note.** The duality pairing is the real inner product (Riesz). No property of $\nabla f$ is needed.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 4.1, fifth display ('For the gradient term …'), p. 17

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

namespace NAGFlow.Implicit

open scoped RealInnerProductSpace

/-- Proof of Theorem 4.1, fifth display, p. 17: if `α_k > 0` and the first line of (72) holds at
step `k`, then
`-α_k ⟪∇f(x_{k+1}), v_{k+1} - x*⟫
  = -⟪∇f(x_{k+1}), x_{k+1} - x_k⟫ - α_k ⟪∇f(x_{k+1}), x_{k+1} - x*⟫`. -/
theorem gradient_split {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (gradf : V → V) (xstar : V) (α : ℕ → ℝ) (x v : ℕ → V) (k : ℕ)
    (hα : 0 < α k) (hx : (1 / α k) • (x (k + 1) - x k) = v (k + 1) - x (k + 1)) :
    -α k * ⟪gradf (x (k + 1)), v (k + 1) - xstar⟫
      = -⟪gradf (x (k + 1)), x (k + 1) - x k⟫
        - α k * ⟪gradf (x (k + 1)), x (k + 1) - xstar⟫ := by sorry

end NAGFlow.Implicit
