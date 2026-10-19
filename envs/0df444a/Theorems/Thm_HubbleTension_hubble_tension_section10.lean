-- Prove2me | Theorems.Thm_HubbleTension_hubble_tension_section10
-- name    : HubbleTension.hubble_tension_section10
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:35:25.656512+00:00
-- url     : https://prove2.me/theorems/1b08683f-9caf-4929-9ad0-ca4fd1de6030
-- title:
--   Hubble tension: $5\sigma$, below $3\sigma$ at $\pm1.5$, $2\sigma$ at $\pm2.0$
-- statement:
--   With $\mathrm{tension}(a,\sigma_a,b,\sigma_b)=|a-b|/\sqrt{\sigma_a^2+\sigma_b^2}$ and the Planck value $67.4 \pm 0.5$: (i) the SH0ES value $73.04 \pm 1.04$ is in tension $t$ with $4.5 \le t < 5.5$ (a $5\sigma$ tension); (ii) a local value $72.0 \pm 1.5$ is in tension less than $3\sigma$; (iii) a local value $72.0 \pm 2.0$ is in tension $t$ with $1.5 \le t < 2.5$ (a $2\sigma$ tension).
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §10, p. 25 (SH0ES value from §3.2, p. 5; Planck value from §1, p. 1)

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem hubble_tension_section10 :
    (4.5 ≤ tension 73.04 1.04 67.4 0.5 ∧ tension 73.04 1.04 67.4 0.5 < 5.5) ∧
    tension 72.0 1.5 67.4 0.5 < 3 ∧
    (1.5 ≤ tension 72.0 2.0 67.4 0.5 ∧ tension 72.0 2.0 67.4 0.5 < 2.5) := by sorry

end HubbleTension
