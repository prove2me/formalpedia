-- Prove2me | Theorems.Thm_GKP1998_swave_radial_solution
-- name    : GKP1998.swave_radial_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:43:29.895668+00:00
-- url     : https://prove2.me/theorems/9880cd4c-fa24-4e35-95d9-4987ff5f8ccb
-- title:
--   Eqs. (20), (22): $z^2K_2(kz)$ solves the massless s-wave radial equation
-- statement:
--   For every $k>0$ and $z>0$, the function $f(w)=w^2K_2(kw)$ satisfies
--   $$z^3\,\partial_z\big(z^{-3}\partial_z f\big)(z)-k^2f(z)=0,$$
--   the momentum-space form of the massless s-wave equation (20); this is the radial wave function of Eqs. (22)–(23).
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 109, Eqs. (20), (22)-(23)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eqs. (20), (22)–(23): for space-like momentum `k > 0`, `z ↦ z² K₂(kz)` solves the
s-wave massless radial equation `z³ ∂_z (z⁻³ ∂_z f) − k² f = 0` on `z > 0`. -/
theorem swave_radial_solution (k z : ℝ) (hk : 0 < k) (hz : 0 < z) :
    throatOperator k 0 (fun w => w ^ 2 * besselK 2 (k * w)) z = 0 := by sorry
end GKP1998
