-- Prove2me | Theorems.Thm_HessianDamping_IGAHDSC_sc_lip_ineqs
-- name    : HessianDamping.IGAHDSC.sc_lip_ineqs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:51.163493+00:00
-- url     : https://prove2.me/theorems/2b99f171-ecfd-48da-b7f6-68da7d9ab3bb
-- title:
--   Proof of Theorem 11, p. 30 — strong-convexity inequalities
-- statement:
--   Let $f:H\to\mathbb R$ be continuously differentiable and $\mu$-strongly convex, where $\mu>0$, and suppose its gradient is $L$-Lipschitz with $L>0$. If $x^*$ minimizes $f$, then for every sequence $(x_k)$ and $k\ge1$,
--   $$f(x^*)\ge f(x_k)+\langle\nabla f(x_k),x^*-x_k\rangle+\frac\mu2\|x_k-x^*\|^2,$$
--   and the chain
--   $$f(x_k)\ge f(x_{k+1})+\langle\nabla f(x_{k+1}),x_k-x_{k+1}\rangle+\frac\mu2\|x_{k+1}-x_k\|^2\ge f(x_{k+1})+\langle\nabla f(x_k),x_k-x_{k+1}\rangle+(\frac\mu2-L)\|x_{k+1}-x_k\|^2.$$
--
--   These are the two displayed estimates used to compare successive objective values and the minimizer in the energy calculation. **Formalization Note** The estimates depend only on the regularity and curvature of $f$; they hold at the points of any sequence, including an IGAHD-SC run.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 30, proof of Theorem 11, two displayed inequalities after the velocity increment

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

namespace HessianDamping.IGAHDSC

/-- The strong-convexity estimates in the proof of Theorem 11, p. 30. -/
theorem sc_lip_ineqs {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u w : H, ‖gradient f u - gradient f w‖ ≤ L * ‖u - w‖)
    (xstar : H) (hxstar : ∀ y : H, f xstar ≤ f y)
    (x : ℕ → H) (k : ℕ) (hk : 1 ≤ k) :
    (f (x k) + inner ℝ (gradient f (x k)) (xstar - x k) +
        μ / 2 * ‖x k - xstar‖ ^ 2 ≤ f xstar) ∧
      (f (x (k + 1)) + inner ℝ (gradient f (x (k + 1))) (x k - x (k + 1)) +
        μ / 2 * ‖x (k + 1) - x k‖ ^ 2 ≤ f (x k)) ∧
      (f (x (k + 1)) + inner ℝ (gradient f (x k)) (x k - x (k + 1)) +
        (μ / 2 - L) * ‖x (k + 1) - x k‖ ^ 2 ≤
        f (x (k + 1)) + inner ℝ (gradient f (x (k + 1))) (x k - x (k + 1)) +
          μ / 2 * ‖x (k + 1) - x k‖ ^ 2) ∧
      (f (x (k + 1)) + inner ℝ (gradient f (x k)) (x k - x (k + 1)) +
        (μ / 2 - L) * ‖x (k + 1) - x k‖ ^ 2 ≤ f (x k)) := by sorry

end HessianDamping.IGAHDSC
