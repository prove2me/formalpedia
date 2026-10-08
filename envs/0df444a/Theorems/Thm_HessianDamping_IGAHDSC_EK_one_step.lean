-- Prove2me | Theorems.Thm_HessianDamping_IGAHDSC_EK_one_step
-- name    : HessianDamping.IGAHDSC.EK_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:58.481178+00:00
-- url     : https://prove2.me/theorems/fac6c931-a9f4-4b82-a0af-f539e7af45cb
-- title:
--   Proof of Theorem 11, p. 32 — one-step energy inequality
-- statement:
--   Let $f$ satisfy the hypotheses of Theorem 11: it is $C^1$ and $\mu$-strongly convex, its gradient is $L$-Lipschitz, $x^*$ minimizes $f$, $s>0$, $0\le\beta\le1/\sqrt\mu$, and (26) holds. For every IGAHD-SC run and $k\ge1$, the energy $E_k$ defined above satisfies
--   $$\frac{E_{k+1}-E_k}{\sqrt s}+\frac{\sqrt\mu}{2}E_{k+1}+\frac\beta2\|\nabla f(x_{k+1})\|^2\le0.$$
--
--   This is the contraction inequality from which the paper obtains geometric energy decay. **Formalization Note** The first bound in (26) is $8\beta L\le\sqrt\mu$, preserving the intended $\beta=0$ case. The paper's proof explicitly uses $\beta\ge0$, which is included.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 32, proof of Theorem 11, final one-step inequality

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

namespace HessianDamping.IGAHDSC

/-- The final one-step energy inequality in the proof of Theorem 11, p. 32. -/
theorem EK_one_step {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u w : H, ‖gradient f u - gradient f w‖ ≤ L * ‖u - w‖)
    (xstar : H) (hxstar : ∀ y : H, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / Real.sqrt μ)
    (hL1 : 8 * β * L ≤ Real.sqrt μ)
    (hL2 : L ≤ (Real.sqrt μ / (2 * s) + μ / Real.sqrt s) /
      (2 * β * μ + 1 / Real.sqrt s + Real.sqrt μ / 2))
    (x : ℕ → H) (hrun : IsIGAHDSCRun f μ β s x)
    (k : ℕ) (hk : 1 ≤ k) :
    1 / Real.sqrt s * (EK f μ β s x xstar (k + 1) - EK f μ β s x xstar k) +
      1 / 2 * Real.sqrt μ * EK f μ β s x xstar (k + 1) +
      β / 2 * ‖gradient f (x (k + 1))‖ ^ 2 ≤ 0 := by sorry

end HessianDamping.IGAHDSC
