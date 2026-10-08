-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_vK_succ_sub
-- name    : HessianDamping.IPAHDSC.vK_succ_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:51.406978+00:00
-- url     : https://prove2.me/theorems/3d480e44-b617-414f-8702-7789ad6862b7
-- title:
--   Proof of Theorem 9, p. 24 — v_{k+1} − v_k = −√µ(x_{k+1} − x_k) − √s∇f(x_{k+1})
-- statement:
--   Let $f:H\to\mathbb R$ be convex and $C^1$, $\mu>0$, $s>0$, $\beta\ge0$, let $x^\star\in H$ and let $(x_k)$ be a run of (IPAHD-SC). With $v_k=\sqrt\mu(x_k-x^\star)+\frac{1}{\sqrt s}(x_k-x_{k-1})+\beta\nabla f(x_k)$, for every $k\ge1$,
--   $$v_{k+1}-v_k=-\sqrt\mu\,(x_{k+1}-x_k)-\sqrt s\,\nabla f(x_{k+1}).$$
--
--   This identity is the first step of the Lyapunov analysis: it expresses the change of the velocity-like vector $v_k$ through the step $x_{k+1}-x_k$ and the new gradient.
--
--   **Formalization Note** $x^\star$ is an arbitrary point here; minimality is not needed for this identity. $s>0$ is the page's implicit positive step size.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 24, proof of Theorem 9, display after "Using successively the definition of v_k and (20)"

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- Proof of Theorem 9, p. 24: along a run of (IPAHD-SC), for `k ≥ 1`,
`v_{k+1} - v_k = -√μ(x_{k+1} - x_k) - √s∇f(x_{k+1})`. -/
theorem vK_succ_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β)
    (xstar : H) (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) (k : ℕ) (hk : 1 ≤ k) :
    vK f μ β s x xstar (k + 1) - vK f μ β s x xstar k =
      -(Real.sqrt μ • (x (k + 1) - x k)) - Real.sqrt s • gradient f (x (k + 1)) := by sorry

end HessianDamping.IPAHDSC
