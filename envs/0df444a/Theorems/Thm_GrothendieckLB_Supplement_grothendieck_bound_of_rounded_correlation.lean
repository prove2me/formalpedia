-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_grothendieck_bound_of_rounded_correlation
-- name    : GrothendieckLB.Supplement.grothendieck_bound_of_rounded_correlation
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T18:43:22.87491+00:00
-- url     : https://prove2.me/theorems/bc3c3099-cdca-457d-b910-24f4ea077254
-- title:
--   The coefficient gap of a rounded correlation bounds all finite bilinear forms
-- statement:
--   Suppose $H(t)=\sum b_kt^k$ on the open real unit interval, with zero constant term and absolutely summable nonlinear coefficients. At every scalar dilation $0<r<1$, assume that matrix averages against $H(r\langle u_i,v_j\rangle)$ are bounded by $\pi/2$ times the sign optimum. Then every $\gamma>0$ such that
--   $$\gamma+\sum_{k\ge 2}|b_k|\le b_1$$
--   gives the real Grothendieck bound $K_G\le\pi/(2\gamma)$.
-- source:
--   Bo Peng, Certified Fourier rounding for the real Grothendieck inequality, arXiv:2610.24417, Proposition 3.1. The statement abstracts the Gaussian rounding inequality and allows radial limits.

import Definitions.Def_GrothendieckConstantDefs

namespace GrothendieckLB.Supplement

open GrothendieckConstant

theorem grothendieck_bound_of_rounded_correlation (H : ℝ → ℝ) (b : ℕ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hser : ∀ t : ℝ, |t| < 1 → HasSum (fun k => b k*t^k) (H t))
    (hzero : b 0=0) (hs : Summable (fun k : ℕ => |b (k+2)|))
    (hgap : γ+(∑' k, |b (k+2)|) ≤ b 1)
    (hround : ∀ (m n d : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
      (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖u i‖=1) → (∀ j, ‖v j‖=1) → ∀ r : ℝ, 0 < r → r < 1 →
        (∑ i, ∑ j, A i j*H (r*inner ℝ (u i) (v j))) ≤ Real.pi/2*optValue A) :
    grothendieckConst ≤ Real.pi/(2*γ) := by sorry

end GrothendieckLB.Supplement
