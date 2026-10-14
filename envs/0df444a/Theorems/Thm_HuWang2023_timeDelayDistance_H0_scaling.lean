-- Prove2me | Theorems.Thm_HuWang2023_timeDelayDistance_H0_scaling
-- name    : HuWang2023.timeDelayDistance_H0_scaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:41:12.162001+00:00
-- url     : https://prove2.me/theorems/fc8138a9-8ae8-4921-b138-46aee8b0e078
-- title:
--   Time-delay distance scales as $1/H_0$
-- statement:
--   For all real $c$, $\Omega_m$, $z_{\rm lens}$, $z_s$ and all nonzero $H_0$, $H_0'$, the time-delay distance of Eq. (1) satisfies
--   $$H_0\,D_{\Delta t}(H_0) = H_0'\,D_{\Delta t}(H_0').$$
--
--   So $H_0 D_{\Delta t}$ does not depend on $H_0$: the time-delay distance is inversely proportional to the Hubble constant, with the remaining cosmological dependence ($\Omega_m$) entering only through the proportionality factor. This is the precise sense in which $D_{\Delta t}$ is "primarily sensitive to $H_0$, with weak dependence on other cosmological parameters".
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 3.1, p. 4, Eq. (1) and the sentence following Eq. (3)

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem timeDelayDistance_H0_scaling (c Ωm zl zs H0 H0' : ℝ)
    (hH0 : H0 ≠ 0) (hH0' : H0' ≠ 0) :
    H0 * timeDelayDistance c H0 Ωm zl zs = H0' * timeDelayDistance c H0' Ωm zl zs := by sorry

end HuWang2023
