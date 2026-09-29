-- Prove2me | Theorems.Thm_Landreman3DEquilibria_divergence_free
-- name    : Landreman3DEquilibria.divergence_free
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:55:53.628426+00:00
-- url     : https://prove2.me/theorems/92bec2ff-2206-4f65-941e-99358d796f0d
-- title:
--   $\nabla\cdot B=0$
-- statement:
--   Let $0<\epsilon<1$ and let $B$ be the field of the integer-transform family. At every point of the domain $U_\epsilon$ the field is solenoidal:
--
--   $$\nabla\cdot B=0 .$$
--
--   This is the second of the two MHD equilibrium equations $(\nabla\times B)\times B=\nabla p$, $\nabla\cdot B=0$. In the source it follows from the fact that $B$ is obtained from a divergence-free axisymmetric field by a constant linear stretch.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.1) with (1.1); divergence-freedom, Section 2.1

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem divergence_free (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec) (hx : x ∈ domainU e) :
    divg (Bfield e) x = 0 := by sorry

end Landreman3DEquilibria
