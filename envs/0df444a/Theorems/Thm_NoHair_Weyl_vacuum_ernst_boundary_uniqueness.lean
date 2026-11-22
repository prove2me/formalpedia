-- Prove2me | Theorems.Thm_NoHair_Weyl_vacuum_ernst_boundary_uniqueness
-- name    : NoHair.Weyl.vacuum_ernst_boundary_uniqueness
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:52:21.777602+00:00
-- url     : https://prove2.me/theorems/413151a7-9b58-4e52-8d8e-1ff8992a3556
-- title:
--   Uniqueness for vacuum Ernst maps with bounded deviation
-- statement:
--   Consider two $C^2$ vacuum Ernst maps $(X_1,Y_1)$ and $(X_2,Y_2)$ on the open Weyl half-plane $\rho>0$, with $X_1,X_2>0$. Suppose their comparison scalar
--
--   $$
--   \sigma=\frac{(X_1-X_2)^2+(Y_1-Y_2)^2}{X_1X_2}
--   $$
--
--   is bounded on the whole half-plane and tends uniformly to zero as $\rho^2+z^2\to\infty$. Then the axial norms and the twist potentials coincide throughout the half-plane,
--
--   $$
--   (X_1,Y_1)=(X_2,Y_2).
--   $$
--
--   The boundedness condition controls the axis and horizon rods, where the individual potentials may be singular. This is the elliptic uniqueness step in the stationary axisymmetric vacuum comparison.
-- source:
--   A. J. Amsel, G. T. Horowitz, D. Marolf and M. M. Roberts, Uniqueness of Extremal Kerr and Kerr–Newman Black Holes, pp. 3–5, eqs. (8)–(13), https://arxiv.org/abs/0906.2367. P. T. Chruściel, J. L. Costa and M. Heusler, Stationary Black Holes: Uniqueness and Beyond, §§8.2, 8.4, pp. 44, 47–48, eqs. (8.13), (8.24), Prop. 8.1, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_vacuumErnst

namespace NoHair.Weyl

theorem vacuum_ernst_boundary_uniqueness (u v : ErnstPotentials)
    (hu : u.IsSolution) (hv : v.IsSolution) (hb : HasComparisonBounds u v) :
    u = v := by
  sorry

end NoHair.Weyl
