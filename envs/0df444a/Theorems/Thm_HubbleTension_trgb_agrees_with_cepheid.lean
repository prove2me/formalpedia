-- Prove2me | Theorems.Thm_HubbleTension_trgb_agrees_with_cepheid
-- name    : HubbleTension.trgb_agrees_with_cepheid
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:30:08.959334+00:00
-- url     : https://prove2.me/theorems/d8647f77-5326-4676-a766-91b98b56dc98
-- title:
--   TRGB $H_0$ agrees with the Cepheid $H_0$ at better than $2\sigma$
-- statement:
--   The tension between the CCHP TRGB value $H_0 = 69.8 \pm 0.6\,(\mathrm{stat}) \pm 1.6\,(\mathrm{sys})$ (errors combined in quadrature) and the SH0ES Cepheid value $H_0 = 73.04 \pm 1.04$ is less than $2\sigma$.
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §4.1, p. 7 (SH0ES value from §3.2, p. 5)

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem trgb_agrees_with_cepheid :
    tension 69.8 (quadSum 0.6 1.6) 73.04 1.04 < 2 := by sorry

end HubbleTension
