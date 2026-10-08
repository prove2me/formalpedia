-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_EK_le
-- name    : HessianDamping.IPAHDSC.EK_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:35.362208+00:00
-- url     : https://prove2.me/theorems/89891edf-0bf2-47de-9c99-ca61751b273a
-- title:
--   (21), proof of Theorem 9, p. 26 — E_k ≤ E₁q^{k−1}
-- statement:
--   Under the hypotheses of Theorem 9 ($f$ convex, $C^1$, $\mu$-strongly convex with $\mu>0$; $x^\star$ a minimizer; $s>0$, $0\le\beta\le\frac{1}{2\sqrt\mu}$, $\sqrt s\le\beta$; $(x_k)$ a run of (IPAHD-SC)), with $q=\frac{1}{1+\frac12\sqrt{\mu s}}$, for every $k\ge1$,
--   $$E_k\le E_1\,q^{k-1}.$$
--
--   This is the exponential decay of the Lyapunov energy, display (21); the objective estimate of Theorem 9 follows from it since $E_k\ge f(x_k)-f(x^\star)$.
--
--   **Formalization Note** $E_1$ is the constant of Theorem 9, which coincides with the energy $E_k$ at $k=1$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 26, proof of Theorem 9, (21)

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- (21), proof of Theorem 9, p. 26: `E_k ≤ E₁ q^(k-1)` for every `k ≥ 1`. -/
theorem EK_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (hsβ : Real.sqrt s ≤ β)
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) :
    ∀ k : ℕ, 1 ≤ k → EK f μ β s x xstar k ≤ E1 f μ β s x xstar * qRate μ s ^ (k - 1) := by sorry

end HessianDamping.IPAHDSC
