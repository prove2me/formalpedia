-- Prove2me | Theorems.Thm_HubbleTension_ngc4258_cepheid_mw_differs_from_maser
-- name    : HubbleTension.ngc4258_cepheid_mw_differs_from_maser
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:29:02.558996+00:00
-- url     : https://prove2.me/theorems/4aa31b24-015c-4840-9c0b-eb6c4fee744b
-- title:
--   NGC 4258: MW-anchored Cepheid modulus differs by 7% at 2σ
-- statement:
--   The Milky-Way-anchored Cepheid modulus $29.242 \pm 0.052$ of NGC 4258 gives a distance smaller than the maser distance (modulus $29.397 \pm 0.033$) by a factor whose excess $d_{\rm maser}/d_{\rm Ceph}-1$ lies in $[0.065, 0.075)$ (i.e. $7\%$), and the tension $t$ between the two moduli satisfies $2 \le t < 3$ (the $2\sigma$ level).
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §5.3, p. 11

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem ngc4258_cepheid_mw_differs_from_maser :
    (0.065 ≤ distanceFromModulus 29.397 / distanceFromModulus 29.242 - 1 ∧
      distanceFromModulus 29.397 / distanceFromModulus 29.242 - 1 < 0.075) ∧
    (2 ≤ tension 29.242 0.052 29.397 0.033 ∧ tension 29.242 0.052 29.397 0.033 < 3) := by sorry

end HubbleTension
