-- Prove2me | Theorems.Thm_HuWang2023_timeDelayDistance_pos
-- name    : HuWang2023.timeDelayDistance_pos
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:42:30.809199+00:00
-- url     : https://prove2.me/theorems/fe471339-dce4-4078-97b9-4610addf9db9
-- title:
--   The time-delay distance is positive
-- statement:
--   Let $c>0$, $H_0>0$, $\Omega_m \ge 0$ and $0 < z_{\rm lens} < z_s$. Then the time-delay distance of Eq. (1), built from the flat-ΛCDM angular diameter distances of Eqs. (2)–(3), is strictly positive:
--   $$D_{\Delta t} = (1+z_{\rm lens})\frac{D_dD_s}{D_{ds}} > 0.$$
--
--   Together with the $1/H_0$ scaling this gives a positive proportionality constant, so a measured time-delay distance fixes $H_0$. Here $E(z)=\sqrt{\Omega_m(1+z)^3+1-\Omega_m}$ is the flat-ΛCDM expansion rate.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 3.1, p. 4, Eqs. (1)–(3)

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem timeDelayDistance_pos (c H0 Ωm zl zs : ℝ) (hc : 0 < c) (hH0 : 0 < H0)
    (hΩm0 : 0 ≤ Ωm) (hzl : 0 < zl) (hzls : zl < zs) :
    0 < timeDelayDistance c H0 Ωm zl zs := by sorry

end HuWang2023
