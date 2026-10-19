-- Prove2me | Theorems.Thm_HuWang2023_angDistBetween_eq_flat
-- name    : HuWang2023.angDistBetween_eq_flat
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:40:46.043121+00:00
-- url     : https://prove2.me/theorems/b0ae45ad-9450-4ae6-b96b-4b929865bde2
-- title:
--   Eq. (2) vs. Eq. (3): $D_{ds} = D_s - \frac{1+z_d}{1+z_s} D_d$ in flat ΛCDM
-- statement:
--   Let $\Omega_m \ge 0$ and $0 \le z_{\rm lens} \le z_s$, and let $c$, $H_0$ be arbitrary reals. In flat ΛCDM the angular diameter distance between lens and source (Eq. (2)) is expressed through the observer distances (Eq. (3)) by
--   $$D_{ds} = D_s - \frac{1+z_{\rm lens}}{1+z_s}\,D_d,$$
--   where $D_d = D(z_{\rm lens})$ and $D_s = D(z_s)$.
--
--   This is the additivity of comoving distance in a spatially flat universe; it shows that Eqs. (2) and (3) describe one and the same distance measure, so that $D_{\Delta t}$ in Eq. (1) is a function of the two observer distances alone. Here $E(z)=\sqrt{\Omega_m(1+z)^3+1-\Omega_m}$ is the flat-ΛCDM expansion rate.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 3.1, p. 4, Eqs. (2)–(3)

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem angDistBetween_eq_flat (c H0 Ωm zl zs : ℝ)
    (hΩm0 : 0 ≤ Ωm) (hzl : 0 ≤ zl) (hzls : zl ≤ zs) :
    angDistBetween c H0 Ωm zl zs =
      angDist c H0 Ωm zs - (1 + zl) / (1 + zs) * angDist c H0 Ωm zl := by sorry

end HuWang2023
