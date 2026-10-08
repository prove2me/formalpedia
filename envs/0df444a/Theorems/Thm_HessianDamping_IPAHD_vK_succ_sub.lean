-- Prove2me | Theorems.Thm_HessianDamping_IPAHD_vK_succ_sub
-- name    : HessianDamping.IPAHD.vK_succ_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:56.370388+00:00
-- url     : https://prove2.me/theorems/5bad18c9-de63-489a-b252-b5d62ff2d933
-- title:
--   Proof of Theorem 4, p. 12 — under (8), v_{k+1} − v_k = h(β_{k+1} + k(β_{k+1} − β_k) − b_khk)∇f(x_{k+1})
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$, $x^\star\in\mathcal H$, $\alpha,h\in\mathbb R$, real sequences $(\beta_k)$, $(b_k)$ and a sequence $(x_k)$ in $\mathcal H$. Put
--   $$v_k:=(\alpha-1)(x_k-x^\star)+k\big(x_k-x_{k-1}+\beta_kh\nabla f(x_k)\big).$$
--   If $k\ge1$ and the discretization (8) holds at $k$,
--   $$k(x_{k+1}-2x_k+x_{k-1})+\alpha(x_{k+1}-x_k)+\beta_khk\big(\nabla f(x_{k+1})-\nabla f(x_k)\big)+b_kh^2k\,\nabla f(x_{k+1})=0,$$
--   then
--   $$v_{k+1}-v_k=h\big(\beta_{k+1}+k(\beta_{k+1}-\beta_k)-b_khk\big)\nabla f(x_{k+1}).$$
--
--   This identity drives the energy estimate of Theorem 4: the increment of $v_k$ is a multiple $hC_k$ of the gradient at the new iterate.
--
--   **Formalization Note.** The statement is purely algebraic and assumes nothing on $f$ beyond the existence of the vectors $\nabla f(x_k)$ (Mathlib's `gradient f`).
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, §3.1.1, proof of Theorem 4, p. 12

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint
import Definitions.Def_HessianDamping_IPAHD_Setting

namespace HessianDamping.IPAHD

/-- Proof of Theorem 4, p. 12: if (8) holds at step `k ≥ 1`, then
`v_{k+1} - v_k = h (β_{k+1} + k (β_{k+1} - β_k) - b_k h k) ∇f(x_{k+1})`. -/
theorem vK_succ_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (xstar : H) (α h : ℝ) (β b : ℕ → ℝ) (x : ℕ → H)
    (k : ℕ) (hk : 1 ≤ k)
    (h8 : (k : ℝ) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) + α • (x (k + 1) - x k)
      + (β k * h * k) • (gradient f (x (k + 1)) - gradient f (x k))
      + (b k * h ^ 2 * k) • gradient f (x (k + 1)) = 0) :
    vK f α h β x xstar (k + 1) - vK f α h β x xstar k
      = (h * (β (k + 1) + k * (β (k + 1) - β k) - b k * h * k)) • gradient f (x (k + 1)) := by sorry

end HessianDamping.IPAHD
