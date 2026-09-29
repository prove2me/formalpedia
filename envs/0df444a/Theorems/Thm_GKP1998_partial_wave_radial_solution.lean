-- Prove2me | Theorems.Thm_GKP1998_partial_wave_radial_solution
-- name    : GKP1998.partial_wave_radial_solution
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:45:58.768343+00:00
-- url     : https://prove2.me/theorems/ea1cddd2-3c57-46c5-94d4-1e86cd60550a
-- title:
--   Eqs. (34)–(35): $z^2K_{l+2}(kz)$ solves the $l$-th partial-wave radial equation
-- statement:
--   For every natural number $l$ and all $k,z>0$, the function $f(w)=w^2K_{l+2}(kw)$ satisfies
--   $$z^3\partial_z\big(z^{-3}\partial_zf\big)(z)-k^2f(z)-\frac{l(l+4)}{z^2}f(z)=0.$$
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 111, Eqs. (34)-(35)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eqs. (34)–(35): for the `l`-th partial wave, `z ↦ z² K_{l+2}(kz)` solves
`z³ ∂_z (z⁻³ ∂_z f) − k² f − l(l+4)/z² · f = 0` on `z > 0`. -/
theorem partial_wave_radial_solution (l : ℕ) (k z : ℝ) (hk : 0 < k) (hz : 0 < z) :
    throatOperator k ((l : ℝ) * ((l : ℝ) + 4))
      (fun w => w ^ 2 * besselK ((l : ℝ) + 2) (k * w)) z = 0 := by sorry
end GKP1998
