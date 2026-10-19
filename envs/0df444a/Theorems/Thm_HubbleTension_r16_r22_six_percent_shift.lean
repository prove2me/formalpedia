-- Prove2me | Theorems.Thm_HubbleTension_r16_r22_six_percent_shift
-- name    : HubbleTension.r16_r22_six_percent_shift
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:27:03.230611+00:00
-- url     : https://prove2.me/theorems/0e32a42b-1d05-4f6a-80ca-9dc72b352eab
-- title:
--   A $-0.123$ mag offset is a $6\%$ shift in $H_0$
-- statement:
--   For every positive velocity $v$ and modulus $\mu$, decreasing the distance modulus by $0.123$ mag increases the inferred Hubble constant by a relative amount $r$ with $0.055 \le r < 0.065$, i.e. by $6\%$ to the quoted precision.
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, Summary, p. 27

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem r16_r22_six_percent_shift (v μ : ℝ) (hv : 0 < v) :
    0.055 ≤ hubbleConstant v (distanceFromModulus (μ - 0.123)) /
        hubbleConstant v (distanceFromModulus μ) - 1 ∧
    hubbleConstant v (distanceFromModulus (μ - 0.123)) /
        hubbleConstant v (distanceFromModulus μ) - 1 < 0.065 := by sorry

end HubbleTension
