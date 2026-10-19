-- Prove2me | Theorems.Thm_HubbleTension_ngc4258_distance
-- name    : HubbleTension.ngc4258_distance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:27:35.513387+00:00
-- url     : https://prove2.me/theorems/c89d0d45-26c6-4229-9cc8-0f79724dcbef
-- title:
--   NGC 4258: modulus 29.397 is 7.6 Mpc
-- statement:
--   The distance $10^{29.397/5+1}$ pc corresponding to the maser distance modulus $29.397$ of NGC 4258 lies in $[7.55\times10^6, 7.65\times10^6)$ pc, i.e. it is $7.6$ Mpc to the quoted precision.
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §5.3, p. 10

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem ngc4258_distance :
    7.55e6 ≤ distanceFromModulus 29.397 ∧ distanceFromModulus 29.397 < 7.65e6 := by sorry

end HubbleTension
