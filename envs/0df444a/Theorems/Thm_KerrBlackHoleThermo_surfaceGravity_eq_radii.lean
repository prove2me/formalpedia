-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_surfaceGravity_eq_radii
-- name    : KerrBlackHoleThermo.surfaceGravity_eq_radii
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:44:23.664756+00:00
-- url     : https://prove2.me/theorems/fa836077-124e-49fd-a225-ed9615e64932
-- title:
--   Kerr surface gravity: $\kappa = (r_+-r_-)/(2(r_+^2+a^2))$
-- statement:
--   Let $M>0$ and $a$ be real numbers with $a^2\le M^2$, and let $r_\pm = M\pm\sqrt{M^2-a^2}$ be the two horizon radii of the Kerr solution. Then the surface gravity of the Kerr horizon,
--   $$\kappa = \frac{\sqrt{M^2-a^2}}{2M\left(M+\sqrt{M^2-a^2}\right)}\qquad\text{(eq. (3.3))},$$
--   satisfies
--   $$\kappa = \frac{1}{2}\,\frac{r_+-r_-}{r_+^2+a^2}.$$
--
--   This is eq. (3.4) of the dissertation; it makes explicit that $\kappa$ vanishes exactly when the two horizons coincide.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 3.1, eqs. (3.3)–(3.4), p. 54

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Milestone, eq. (3.4): the surface gravity in terms of the horizon radii,
`κ = (r₊ − r₋) / (2 (r₊² + a²))`. -/
theorem surfaceGravity_eq_radii (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    surfaceGravity M a = (rPlus M a - rMinus M a) / (2 * (rPlus M a ^ 2 + a ^ 2)) := by
  sorry

end KerrBlackHoleThermo
