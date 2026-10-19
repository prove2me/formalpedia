-- Prove2me | Theorems.Thm_HubbleTension_modulus_error_percent
-- name    : HubbleTension.modulus_error_percent
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:28:13.385239+00:00
-- url     : https://prove2.me/theorems/75a8dde9-5fd7-4bdc-b750-5ff8ceb1d309
-- title:
--   $\pm0.033$ mag is a $1.5\%$ distance measurement
-- statement:
--   For every distance modulus $\mu$, increasing $\mu$ by $0.033$ mag increases the distance by a relative amount $r$ with $0.0145 \le r < 0.0155$, i.e. $1.5\%$ to the quoted precision.
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §5.3, p. 10

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem modulus_error_percent (μ : ℝ) :
    0.0145 ≤ (distanceFromModulus (μ + 0.033) - distanceFromModulus μ) / distanceFromModulus μ ∧
    (distanceFromModulus (μ + 0.033) - distanceFromModulus μ) / distanceFromModulus μ < 0.0155 := by sorry

end HubbleTension
