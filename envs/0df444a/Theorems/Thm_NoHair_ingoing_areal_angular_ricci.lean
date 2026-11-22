-- Prove2me | Theorems.Thm_NoHair_ingoing_areal_angular_ricci
-- name    : NoHair.ingoing_areal_angular_ricci
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:08:00.279484+00:00
-- url     : https://prove2.me/theorems/85165353-5225-4fd9-be75-4d4a4264d220
-- title:
--   Angular Ricci curvature of an ingoing spherical metric with arbitrary lapse
-- statement:
--   Let $A$ be differentiable throughout $(R,\infty)$. In coordinates $(v,r,z,\varphi)$ with $z=\cos\theta$, consider the spherical metric
--   $$
--   G=-A(r)\,dv^2+2\,dv\,dr+r^2\left(\frac{dz^2}{1-z^2}+(1-z^2)\,d\varphi^2\right).
--   $$
--   At each $r>0$ with $r>R$, its azimuthal Ricci component on the equator at $v=z=\varphi=0$ is
--   $$
--   \operatorname{Ric}(G)_{\varphi\varphi}=1-A(r)-rA'(r).
--   $$
--   The identity holds for an arbitrary radial lapse coefficient, independently of the vacuum equations.
-- source:
--   Direct calculation from the Riemann and Ricci definitions in NoHair_coordinates, applied to the spherical metric in ingoing areal coordinates. This angular component underlies the radial vacuum equation in the Schwarzschild derivation, see S. Carroll, Lecture Notes on General Relativity, Section 7, https://arxiv.org/abs/gr-qc/9712019.

import Definitions.Def_NoHair_coordinates

open NoHair

theorem NoHair.ingoing_areal_angular_ricci (A : ℝ → ℝ) (R r : ℝ)
    (hr : 0 < r) (hR : R < r) (hA : ∀ s, R < s → DifferentiableAt ℝ A s) :
    let G := fun y : E4 => !![-A (y 1), 1, 0, 0;
      1, 0, 0, 0; 0, 0, y 1 ^ 2 / (1 - y 2 ^ 2), 0;
      0, 0, 0, y 1 ^ 2 * (1 - y 2 ^ 2)]
    ricci G (WithLp.toLp 2 ![0, r, 0, 0]) 3 3 = 1 - A r - r * deriv A r := by sorry
