-- Prove2me | Theorems.Thm_HessianDamping_IGAHD_EK_succ_sub_le
-- name    : HessianDamping.IGAHD.EK_succ_sub_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:00.177027+00:00
-- url     : https://prove2.me/theorems/9ed453c4-3fa2-43df-bdf3-e82433d55ae6
-- title:
--   §3.2, p. 17 — energy increment bounded by B_k
-- statement:
--   For an IGAHD run under Theorem 6's assumptions, and $k\ge1$ with $t_{k+1}\ge1$, the energy $E_k$ of (14) and the quantity $B_k$ defined on p. 17 satisfy
--
--   $$E_{k+1}-E_k\le-t_{k+1}B_k.$$
--
--   Here $B_k=t_{k+1}\beta\sqrt{s}\langle\nabla f(y_k),\nabla f(x_k)\rangle+\frac{s}{2}(t_{k+1}-1)\|\nabla f(x_k)-\nabla f(y_k)\|^2+\frac{s}{2}\|\nabla f(y_k)\|^2$. This estimate is the displayed energy relation behind the later rate and summability conclusions.
--
--   **Formalization Note** The source's argument works where $t_{k+1}-1\ge0$, encoded as $k\ge\alpha-1$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 17, proof of Theorem 6, E-increment and B_k

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

namespace HessianDamping.IGAHD

/-- The E-increment bound in the proof of Theorem 6, p. 17. -/
theorem EK_succ_sub_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y)
    (k : ℕ) (hk : 1 ≤ k) (hkt : α - 1 ≤ (k : ℝ)) :
    EK f α β s x xstar (k + 1) - EK f α β s x xstar k ≤
      -tK α (k + 1) * BK f α β s x y k := by sorry
end HessianDamping.IGAHD
