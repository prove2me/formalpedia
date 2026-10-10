-- Prove2me | Theorems.Thm_NAGFlow_Implicit_last_term_identity
-- name    : NAGFlow.Implicit.last_term_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:58.932369+00:00
-- url     : https://prove2.me/theorems/7e05b5f3-48f2-4a6f-99ee-d685cbc977ba
-- title:
--   Proof of Theorem 4.1, second display, p. 17 — γ_k(v_{k+1} − v_k, (v_{k+1} + v_k)/2 − x*) split
-- statement:
--   Let $V$ be a real Hilbert space, $x^*\in V$, $(v_k)$ a sequence in $V$ and $(\gamma_k)$ a real sequence. For every $k$,
--
--   $$\gamma_k\left(v_{k+1}-v_k,\tfrac{v_{k+1}+v_k}2-x^*\right)=\gamma_k\left(v_{k+1}-v_k,v_{k+1}-x^*\right)-\frac{\gamma_k}2\|v_{k+1}-v_k\|^2 .$$
--
--   This identity isolates the negative square $-\frac{\gamma_k}2\|v_{k+1}-v_k\|^2$, which the proof of Theorem 4.1 later drops, and leaves a cross term to which the second line of the scheme (72) applies.
--
--   **Formalization Note.** It is an identity in any real inner product space and needs no hypothesis on the sequences.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 4.1, second display, p. 17

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

namespace NAGFlow.Implicit

open scoped RealInnerProductSpace

/-- Proof of Theorem 4.1, second display, p. 17: for any sequences `v`, `γ`, any `x*` and `k`,
`γ_k ⟪v_{k+1} - v_k, (v_{k+1} + v_k)/2 - x*⟫
  = γ_k ⟪v_{k+1} - v_k, v_{k+1} - x*⟫ - γ_k/2 ‖v_{k+1} - v_k‖²`. -/
theorem last_term_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (xstar : V) (γ : ℕ → ℝ) (v : ℕ → V) (k : ℕ) :
    γ k * ⟪v (k + 1) - v k, (1 / 2 : ℝ) • (v (k + 1) + v k) - xstar⟫
      = γ k * ⟪v (k + 1) - v k, v (k + 1) - xstar⟫ - γ k / 2 * ‖v (k + 1) - v k‖ ^ 2 := by sorry

end NAGFlow.Implicit
