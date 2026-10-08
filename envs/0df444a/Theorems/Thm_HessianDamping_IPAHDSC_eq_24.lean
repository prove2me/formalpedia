-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_eq_24
-- name    : HessianDamping.IPAHDSC.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:55.432793+00:00
-- url     : https://prove2.me/theorems/1d4ab1a9-9149-4979-a0ac-ff7e56e1c034
-- title:
--   (24), proof of Theorem 9, p. 27 — θβ²√s Σ_{p=0}^{k−2} θ^p‖∇f(x_{k−p})‖² ≤ θ^{k−1}Z₁ + (4E₁/√µ)q^{k−1}
-- statement:
--   Under the hypotheses of Theorem 9, with $\theta=\frac{1}{1+\sqrt{\mu s}}$, $q=\frac{1}{1+\frac12\sqrt{\mu s}}$ and $Z_k$ as in (22), for every $k\ge2$,
--   $$\theta\beta^2\sqrt s\sum_{p=0}^{k-2}\theta^p\|\nabla f(x_{k-p})\|^2\le\theta^{k-1}Z_1+\frac{4E_1}{\sqrt\mu}q^{k-1}.$$
--
--   Reindexing this discounted sum of squared gradients gives the gradient estimate of Theorem 9.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 27, proof of Theorem 9, (24)

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- (24), proof of Theorem 9, p. 27: for all `k ≥ 2`,
`θβ²√s Σ_{p=0}^{k-2} θ^p ‖∇f(x_{k-p})‖² ≤ θ^(k-1) Z₁ + (4E₁/√μ) q^(k-1)`. -/
theorem eq_24 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : HessianDamping.DINSC.IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (hsβ : Real.sqrt s ≤ β)
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) :
    ∀ k : ℕ, 2 ≤ k →
      thetaRate μ s * β ^ 2 * Real.sqrt s *
          ∑ p ∈ Finset.range (k - 1), thetaRate μ s ^ p * ‖gradient f (x (k - p))‖ ^ 2 ≤
        thetaRate μ s ^ (k - 1) * ZK f μ β x xstar 1 +
          4 * E1 f μ β s x xstar / Real.sqrt μ * qRate μ s ^ (k - 1) := by sorry

end HessianDamping.IPAHDSC
