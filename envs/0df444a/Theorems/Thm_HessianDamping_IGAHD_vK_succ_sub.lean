-- Prove2me | Theorems.Thm_HessianDamping_IGAHD_vK_succ_sub
-- name    : HessianDamping.IGAHD.vK_succ_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:59.096614+00:00
-- url     : https://prove2.me/theorems/684f77cf-4ac4-4400-b5bf-a7ed8dceaaef
-- title:
--   §3.2, p. 16 — increment of v_k
-- statement:
--   For an IGAHD run and $k\ge1$, the auxiliary vector $v_k$ of (15) satisfies
--
--   $$v_{k+1}-v_k=-s\,t_{k+1}\nabla f(y_k).$$
--
--   The identity aligns the energy's vector term with the gradient step in the algorithm and is used in the one-step energy estimate.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 16, proof of Theorem 6, v-increment

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

namespace HessianDamping.IGAHD

/-- The v-increment identity in the proof of Theorem 6, p. 16. -/
theorem vK_succ_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y)
    (k : ℕ) (hk : 1 ≤ k) :
    vK f α β s x xstar (k + 1) - vK f α β s x xstar k =
      -(s * tK α (k + 1)) • gradient f (y k) := by sorry
end HessianDamping.IGAHD
