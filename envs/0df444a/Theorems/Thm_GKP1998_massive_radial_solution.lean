-- Prove2me | Theorems.Thm_GKP1998_massive_radial_solution
-- name    : GKP1998.massive_radial_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:52:23.879184+00:00
-- url     : https://prove2.me/theorems/db807afc-e61c-4db3-b5c5-8cb99decc6e0
-- title:
--   Eqs. (39)–(41): $z^2K_\nu(kz)$, $\nu=\sqrt{4+(mR)^2}$, solves the massive radial equation
-- statement:
--   For all $m,R,k,z>0$, with $\nu=\sqrt{4+(mR)^2}$, the function $f(w)=w^2K_\nu(kw)$ satisfies
--   $$z^3\partial_z\big(z^{-3}\partial_zf\big)(z)-k^2f(z)-\frac{(mR)^2}{z^2}f(z)=0,$$
--   the throat-region equation (40) of a scalar string state of mass $m$.
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 112, Eqs. (39)-(41)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eqs. (39)–(41): in the throat region a scalar string state of mass `m` obeys the radial
equation with centrifugal coefficient `(mR)²`, and `z ↦ z² K_ν(kz)` with
`ν = √(4 + (mR)²)` solves it on `z > 0`. -/
theorem massive_radial_solution (m R k z : ℝ) (hm : 0 < m) (hR : 0 < R) (hk : 0 < k)
    (hz : 0 < z) :
    throatOperator k ((m * R) ^ 2) (fun w => w ^ 2 * besselK (massiveOrder m R) (k * w)) z
      = 0 := by sorry
end GKP1998
