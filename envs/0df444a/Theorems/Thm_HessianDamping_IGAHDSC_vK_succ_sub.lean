-- Prove2me | Theorems.Thm_HessianDamping_IGAHDSC_vK_succ_sub
-- name    : HessianDamping.IGAHDSC.vK_succ_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:06.376383+00:00
-- url     : https://prove2.me/theorems/7ea2ac46-4305-410e-b190-029bc28c7a79
-- title:
--   Proof of Theorem 11, p. 30 — auxiliary vector increment
-- statement:
--   Let $f:H\to\mathbb R$, let $\mu,s>0$, and let $(x_k)$ satisfy IGAHD-SC from arbitrary $x_0,x_1$. For any reference point $x^*$ and every $k\ge1$, the auxiliary vector $v_k$ defined above satisfies
--   $$v_{k+1}-v_k=-\sqrt\mu(x_{k+1}-x_k)-\sqrt s\,\nabla f(x_k).$$
--
--   This identity connects the explicit algorithm to the energy difference used later in the proof. **Formalization Note** The recurrence starts at $k=1$, so no truncated natural subtraction is used at $k=0$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 30, proof of Theorem 11, displayed velocity increment

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

namespace HessianDamping.IGAHDSC

/-- The velocity increment in the proof of Theorem 11, p. 30. -/
theorem vK_succ_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (μ β s : ℝ) (hμ : 0 < μ) (hs : 0 < s)
    (xstar : H) (x : ℕ → H) (hrun : IsIGAHDSCRun f μ β s x)
    (k : ℕ) (hk : 1 ≤ k) :
    vK f μ β s x xstar (k + 1) - vK f μ β s x xstar k =
      -(Real.sqrt μ) • (x (k + 1) - x k) -
        Real.sqrt s • gradient f (x k) := by sorry

end HessianDamping.IGAHDSC
