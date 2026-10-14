-- Prove2me | Theorems.Thm_HubbleTension_hubbleConstant_modulus_shift
-- name    : HubbleTension.hubbleConstant_modulus_shift
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:24:09.429097+00:00
-- url     : https://prove2.me/theorems/e1c742ab-c4ec-41cf-88b4-171c74d18260
-- title:
--   Hubble's law under a distance-modulus shift
-- statement:
--   For a fixed recession velocity $v$, replacing a distance modulus $\mu$ by $\mu+\Delta$ multiplies the Hubble constant $H_0 = v/d$ inferred from Hubble's law by $10^{-\Delta/5}$.
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, Summary pp. 26-27 (Hubble's law v = H0 d, §1)

import Mathlib
import Definitions.Def_HubbleTension_Defs

namespace HubbleTension

theorem hubbleConstant_modulus_shift (v μ Δ : ℝ) :
    hubbleConstant v (distanceFromModulus (μ + Δ)) =
      (10 : ℝ) ^ (-Δ / 5) * hubbleConstant v (distanceFromModulus μ) := by sorry

end HubbleTension
