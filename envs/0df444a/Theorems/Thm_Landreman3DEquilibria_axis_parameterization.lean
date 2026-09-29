-- Prove2me | Theorems.Thm_Landreman3DEquilibria_axis_parameterization
-- name    : Landreman3DEquilibria.axis_parameterization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:16:25.245289+00:00
-- url     : https://prove2.me/theorems/333af735-f719-42ec-b6e2-553050088c9d
-- title:
--   The magnetic axis $\gamma(\zeta)$, eq. (2.19)
-- statement:
--   Let $0<\epsilon<1$. The field line with labels $u=-\epsilon/2$, $v=0$ — the one on which $\psi$ attains its minimum value $0$ — is the closed curve
--
--   $$\gamma(\zeta)=\Big(\sqrt{1-\epsilon^2}\,\cos\zeta,\ \sqrt{1-\epsilon^2}\,\sin\zeta,\ \frac{\epsilon}{2}\sin 2\zeta\Big),$$
--
--   and $\psi$ vanishes identically on it. Thus the magnetic axis has constant major radius $R_a=\sqrt{1-\epsilon^2}$ while its elevation $Z_a=(\epsilon/2)\sin2\zeta$ oscillates, so for $\epsilon\neq0$ the axis is a non-planar closed curve — one of the features distinguishing this family from axisymmetric equilibria.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.19) together with the labels u = -ε/2, v = 0 from Section 2.3

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem axis_parameterization (e z : ℝ) (he : 0 < e) (he1 : e < 1) :
    posMap e (-(e / 2)) 0 z = axisCurve e z ∧ psiFun e (axisCurve e z) = 0 := by sorry

end Landreman3DEquilibria
