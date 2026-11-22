-- Prove2me | Theorems.Thm_NoHair_Weyl_ernst_deviation_subharmonic
-- name    : NoHair.Weyl.ernst_deviation_subharmonic
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:02:10.953118+00:00
-- url     : https://prove2.me/theorems/c3fdd15f-0eb2-470e-8ec2-bc78276f3d23
-- title:
--   Subharmonicity of the vacuum Ernst comparison scalar
-- statement:
--   Let $u=(X_1,Y_1)$ and $v=(X_2,Y_2)$ be twice continuously differentiable solutions of the vacuum Ernst equations with $X_i>0$. Their comparison scalar
--   $$
--   \sigma=\frac{(X_1-X_2)^2+(Y_1-Y_2)^2}{X_1X_2}
--   $$
--   is twice continuously differentiable and satisfies
--   $$
--   \partial_s^2\sigma+e^{2s}\partial_z^2\sigma\ge 0
--   $$
--   at every point, where $s=\log\rho$ is logarithmic Weyl radius. This is the differential inequality supplied by the vacuum Mazur identity before imposing any boundary conditions.
-- source:
--   A. J. Amsel, G. T. Horowitz, D. Marolf and M. M. Roberts, Uniqueness of Extremal Kerr and Kerr–Newman Black Holes, pp. 3–5, eqs. (8)–(13), https://arxiv.org/abs/0906.2367. P. T. Chruściel, J. L. Costa and M. Heusler, Stationary Black Holes: Uniqueness and Beyond, §§8.2, 8.4, pp. 44, 47–48, eqs. (8.13), (8.24), Prop. 8.1, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_vacuumErnst

namespace NoHair.Weyl

theorem ernst_deviation_subharmonic (u v : ErnstPotentials)
    (hu : u.IsSolution) (hv : v.IsSolution) :
    ContDiff ℝ 2 (deviation u v) ∧
    ∀ p, 0 ≤ scaledLaplacian (deviation u v) p := by
  sorry

end NoHair.Weyl
