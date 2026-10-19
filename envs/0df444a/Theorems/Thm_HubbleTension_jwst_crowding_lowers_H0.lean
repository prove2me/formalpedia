-- Prove2me | Theorems.Thm_HubbleTension_jwst_crowding_lowers_H0
-- name    : HubbleTension.jwst_crowding_lowers_H0
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:26:33.304482+00:00
-- url     : https://prove2.me/theorems/b6370175-941c-4bf6-8a82-adeada96647d
-- title:
--   A modulus $+0.45$ mag farther lowers $H_0$
-- statement:
--   For every positive recession velocity $v$ and every distance modulus $\mu$, the Hubble constant inferred at modulus $\mu+0.45$ is strictly smaller than the one inferred at $\mu$.
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, Summary, p. 26

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem jwst_crowding_lowers_H0 (v μ : ℝ) (hv : 0 < v) :
    hubbleConstant v (distanceFromModulus (μ + 0.45)) < hubbleConstant v (distanceFromModulus μ) := by sorry

end HubbleTension
