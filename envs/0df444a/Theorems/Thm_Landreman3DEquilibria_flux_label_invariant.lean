-- Prove2me | Theorems.Thm_Landreman3DEquilibria_flux_label_invariant
-- name    : Landreman3DEquilibria.flux_label_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:04:59.373989+00:00
-- url     : https://prove2.me/theorems/a9f394e5-1c14-44e8-97d8-a13bc3f477b1
-- title:
--   $B\cdot\nabla\psi=0$: pressure surfaces are invariant
-- statement:
--   Let $0<\epsilon<1$ and let $\psi$ be the flux label of the integer-transform family. At every point of $U_\epsilon$,
--
--   $$B\cdot\nabla\psi=0 .$$
--
--   Hence $\psi$, and therefore the pressure $p=p_a-2\psi$, is constant along every magnetic field line, so the level sets of $\psi$ are invariant surfaces for the field. This is the property that gives the equilibrium nested flux surfaces, and in the source it is deduced from the force-balance relation $(\nabla\times B)\times B=\nabla p$ by contracting with $B$.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.5), final sentence: 'In particular, B · ∇ψ = 0 follows from (2.5)'

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem flux_label_invariant (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) :
    advect (Bfield e) (psiFun e) x = 0 := by sorry

end Landreman3DEquilibria
