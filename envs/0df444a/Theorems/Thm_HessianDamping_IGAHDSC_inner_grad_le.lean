-- Prove2me | Theorems.Thm_HessianDamping_IGAHDSC_inner_grad_le
-- name    : HessianDamping.IGAHDSC.inner_grad_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:07.112983+00:00
-- url     : https://prove2.me/theorems/41e1e736-827f-4a93-9644-ca708cf5ca4b
-- title:
--   Proof of Theorem 11, p. 31 — gradient inner-product majorization
-- statement:
--   Let $f:H\to\mathbb R$ be continuously differentiable with $L$-Lipschitz gradient, where $L>0$, and let $x^*$ minimize $f$. For every sequence $(x_k)$ and $k\ge1$,
--   $$\langle\nabla f(x_k),x_k-x^*\rangle\le L\|x_k-x^*\|^2\le2L\|x_{k+1}-x^*\|^2+2L\|x_{k+1}-x_k\|^2.$$
--
--   This is the proof's bound for the gradient term that appears in the energy inequality. **Formalization Note** Differentiability at the minimizer gives $\nabla f(x^*)=0$. The bound itself holds for any sequence; the algorithm is used in later milestones.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 31, proof of Theorem 11, gradient majorization display

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

namespace HessianDamping.IGAHDSC

/-- The gradient majorization in the proof of Theorem 11, p. 31. -/
theorem inner_grad_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC1 : ContDiff ℝ 1 f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u w : H, ‖gradient f u - gradient f w‖ ≤ L * ‖u - w‖)
    (xstar : H) (hxstar : ∀ y : H, f xstar ≤ f y)
    (x : ℕ → H) (k : ℕ) (hk : 1 ≤ k) :
    inner ℝ (gradient f (x k)) (x k - xstar) =
      inner ℝ (gradient f (x k) - gradient f xstar) (x k - xstar) ∧
    inner ℝ (gradient f (x k)) (x k - xstar) ≤ L * ‖x k - xstar‖ ^ 2 ∧
      L * ‖x k - xstar‖ ^ 2 ≤
        2 * L * ‖x (k + 1) - xstar‖ ^ 2 +
          2 * L * ‖x (k + 1) - x k‖ ^ 2 := by sorry

end HessianDamping.IGAHDSC
