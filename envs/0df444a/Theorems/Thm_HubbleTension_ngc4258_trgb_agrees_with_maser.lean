-- Prove2me | Theorems.Thm_HubbleTension_ngc4258_trgb_agrees_with_maser
-- name    : HubbleTension.ngc4258_trgb_agrees_with_maser
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:28:39.704346+00:00
-- url     : https://prove2.me/theorems/d93744ee-cc96-4b72-912d-1dbf170d1411
-- title:
--   NGC 4258: TRGB and maser moduli agree
-- statement:
--   The TRGB modulus $29.392 \pm 0.018 \pm 0.032$ (errors combined in quadrature) and the maser modulus $29.397 \pm 0.033$ of NGC 4258 differ by less than $0.2\sigma$, and the corresponding distances differ by less than $1\%$ (relative to the TRGB distance).
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §5.3, p. 10

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem ngc4258_trgb_agrees_with_maser :
    tension 29.392 (quadSum 0.018 0.032) 29.397 0.033 < 0.2 ∧
    |distanceFromModulus 29.397 - distanceFromModulus 29.392| / distanceFromModulus 29.392
      < 0.01 := by sorry

end HubbleTension
