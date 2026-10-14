-- Prove2me | Theorems.Thm_HubbleTension_lmc_deb_distance
-- name    : HubbleTension.lmc_deb_distance
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:29:27.232215+00:00
-- url     : https://prove2.me/theorems/c8de153f-3996-4910-8412-cb9250112b54
-- title:
--   LMC: 1.2% distance uncertainty, ~1% from the Key Project
-- statement:
--   (i) For every modulus $\mu$, an increase by $\sqrt{0.004^2+0.026^2}$ mag increases the distance by a relative amount in $[0.0115, 0.0125)$ ($1.2\%$). (ii) The Key Project LMC distance (modulus $18.5$) exceeds the eclipsing-binary distance (modulus $18.477$) by a relative amount in $[0.005, 0.015)$ ($\sim1\%$).
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §5.1, p. 9

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem lmc_deb_distance (μ : ℝ) :
    (0.0115 ≤ (distanceFromModulus (μ + quadSum 0.004 0.026) - distanceFromModulus μ) /
        distanceFromModulus μ ∧
      (distanceFromModulus (μ + quadSum 0.004 0.026) - distanceFromModulus μ) /
        distanceFromModulus μ < 0.0125) ∧
    (0.005 ≤ (distanceFromModulus 18.5 - distanceFromModulus 18.477) / distanceFromModulus 18.477 ∧
      (distanceFromModulus 18.5 - distanceFromModulus 18.477) / distanceFromModulus 18.477
        < 0.015) := by sorry

end HubbleTension
