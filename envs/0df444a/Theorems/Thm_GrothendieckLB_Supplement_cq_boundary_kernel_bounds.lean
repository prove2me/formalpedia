-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_kernel_bounds
-- name    : GrothendieckLB.Supplement.cq_boundary_kernel_bounds
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T17:00:42.923922+00:00
-- url     : https://prove2.me/theorems/ce0cc886-008e-4d5f-b798-8c31004d1228
-- title:
--   Uniform bounds for the cubic–quintic Gaussian kernel on the unit circle
-- statement:
--   Let $\rho(z)=(z-az^3+bz^5)/(1+a+b)$, where $a=0.34101124^2$ and $b=0.05276111^2$. For $|z|=1$ one has $|1-\rho(z)^2|\ge 0.3724$. Writing $d=1-\rho(z)^2$, one also has $\operatorname{Re}(1/d)-|\operatorname{Re}(\rho(z)/d)|\ge 1/2$. These uniform bounds control the Gaussian moments and the differentiated kernels entering the third-order coefficient estimate.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C. The circle checks are implemented in https://github.com/trishullab/grothendieck-bounds/blob/17de8e2331859d37322c199a3d56fb81d740764f/upper-bounds/theorem-cubic-quintic/certify_d3h.py.

import Mathlib.Analysis.Complex.Basic

namespace GrothendieckLB.Supplement

theorem cq_boundary_kernel_bounds (z : ℂ) (hz : ‖z‖ = 1) :
    let a : ℝ := 0.34101124^2
    let b : ℝ := 0.05276111^2
    let ρ := (z-(a:ℂ)*z^3+(b:ℂ)*z^5) / ((1+a+b : ℝ) : ℂ)
    0.3724 ≤ ‖1-ρ^2‖ ∧ (1/2 : ℝ) ≤ ((1-ρ^2)⁻¹).re - |(ρ/(1-ρ^2)).re| := by sorry

end GrothendieckLB.Supplement
