-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_eq_22
-- name    : HessianDamping.IPAHDSC.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:47.842132+00:00
-- url     : https://prove2.me/theorems/6379f93d-b2a1-42f8-9973-4d702617c48c
-- title:
--   (22), proof of Theorem 9, p. 27 — (1/√s)(Z_k − Z_{k−1}) + √µZ_k + β²‖∇f(x_k)‖² ≤ 2E₁q^{k−1}
-- statement:
--   Under the hypotheses of Theorem 9, let $Z_k=2\beta(f(x_k)-f(x^\star))+\sqrt\mu\|x_k-x^\star\|^2$ and $q=\frac{1}{1+\frac12\sqrt{\mu s}}$. Then for every $k\ge1$,
--   $$\frac{1}{\sqrt s}(Z_k-Z_{k-1})+\sqrt\mu\,Z_k+\beta^2\|\nabla f(x_k)\|^2\le 2E_1q^{k-1}.$$
--
--   This linear recursive inequality for $Z_k$ is the route from the energy decay to the exponential decay of the gradients.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 27, proof of Theorem 9, (22)

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- (22), proof of Theorem 9, p. 27: for all `k ≥ 1`,
`(1/√s)(Z_k - Z_{k-1}) + √μ Z_k + β²‖∇f(x_k)‖² ≤ 2E₁q^(k-1)`. -/
theorem eq_22 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (hsβ : Real.sqrt s ≤ β)
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) :
    ∀ k : ℕ, 1 ≤ k →
      1 / Real.sqrt s * (ZK f μ β x xstar k - ZK f μ β x xstar (k - 1)) +
          Real.sqrt μ * ZK f μ β x xstar k + β ^ 2 * ‖gradient f (x k)‖ ^ 2 ≤
        2 * E1 f μ β s x xstar * qRate μ s ^ (k - 1) := by sorry

end HessianDamping.IPAHDSC
