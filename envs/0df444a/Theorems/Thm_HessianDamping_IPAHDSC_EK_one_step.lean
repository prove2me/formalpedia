-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_EK_one_step
-- name    : HessianDamping.IPAHDSC.EK_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:44.773684+00:00
-- url     : https://prove2.me/theorems/33adc867-055a-4211-99b0-069f75ed685a
-- title:
--   Proof of Theorem 9, p. 26 — (1/√s)(E_{k+1} − E_k) + ½√µE_{k+1} ≤ 0
-- statement:
--   Let $f:H\to\mathbb R$ be convex, $C^1$ and $\mu$-strongly convex with $\mu>0$, let $x^\star$ minimize $f$, let $s>0$ and $0\le\beta\le\frac{1}{2\sqrt\mu}$ with $\sqrt s\le\beta$, and let $(x_k)$ be a run of (IPAHD-SC). With $E_k=f(x_k)-f(x^\star)+\frac12\|v_k\|^2$, for every $k\ge1$,
--   $$\frac{1}{\sqrt s}(E_{k+1}-E_k)+\frac12\sqrt\mu\,E_{k+1}\le0.$$
--
--   This is the discrete Lyapunov inequality behind Theorem 9; it says the energy contracts by the factor $q=1/(1+\frac12\sqrt{\mu s})$ at each step.
--
--   **Formalization Note** The minimizer is given as a point $x^\star$ with $f(x^\star)\le f(y)$ for all $y$ (the standing assumption $\operatorname{argmin}f\neq\emptyset$). $s>0$ is the page's implicit positive step size.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 26, proof of Theorem 9, display after "Let us put the above results together"

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- Proof of Theorem 9, p. 26: under `0 ≤ β ≤ 1/(2√μ)` and `√s ≤ β`, for `k ≥ 1`,
`(1/√s)(E_{k+1} - E_k) + ½√μ E_{k+1} ≤ 0`. -/
theorem EK_one_step {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (hsβ : Real.sqrt s ≤ β)
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) (k : ℕ) (hk : 1 ≤ k) :
    1 / Real.sqrt s * (EK f μ β s x xstar (k + 1) - EK f μ β s x xstar k) +
      1 / 2 * Real.sqrt μ * EK f μ β s x xstar (k + 1) ≤ 0 := by sorry

end HessianDamping.IPAHDSC
