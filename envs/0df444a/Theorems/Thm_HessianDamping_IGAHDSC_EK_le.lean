-- Prove2me | Theorems.Thm_HessianDamping_IGAHDSC_EK_le
-- name    : HessianDamping.IGAHDSC.EK_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:22.936749+00:00
-- url     : https://prove2.me/theorems/5ff1452a-413b-43da-a3a5-f642f68f3b2b
-- title:
--   Proof of Theorem 11, p. 32 — geometric energy bound
-- statement:
--   Under the hypotheses of Theorem 11, let $(x_k)$ be an IGAHD-SC run and let $E_k$ be its energy. With $q=(1+\frac12\sqrt{\mu s})^{-1}$, for every $k\ge1$,
--   $$E_k\le E_1 q^{k-1}.$$
--
--   The estimate is the displayed energy bound that leads to geometric decay of objective error and iterate distance. **Formalization Note** The initial energy $E_1$ uses the free points $x_0,x_1$. As in the one-step claim, the first bound in (26) is expressed without division by $\beta$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 32, proof of Theorem 11, displayed energy bound

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

namespace HessianDamping.IGAHDSC

/-- The geometric energy bound in the proof of Theorem 11, p. 32. -/
theorem EK_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
    EK f μ β s x xstar k ≤ EK f μ β s x xstar 1 * HessianDamping.IPAHDSC.qRate μ s ^ (k - 1) := by sorry

end HessianDamping.IGAHDSC
