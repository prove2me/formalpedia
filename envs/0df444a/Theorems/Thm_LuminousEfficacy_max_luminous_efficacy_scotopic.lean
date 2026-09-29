-- Prove2me | Theorems.Thm_LuminousEfficacy_max_luminous_efficacy_scotopic
-- name    : LuminousEfficacy.max_luminous_efficacy_scotopic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:40:09.301117+00:00
-- url     : https://prove2.me/theorems/d53b4a3d-2d90-41aa-9346-ccd32cb16b44
-- title:
--   Maximum possible scotopic luminous efficacy of radiation is $1700\ \mathrm{lm/W}$
-- statement:
--   The scotopic counterpart of the goal theorem: "Scotopic luminous efficacy of radiation reaches a maximum of $1700$ lm/W for monochromatic light at a wavelength of $507$ nm." With $V$ the scotopic luminosity function (peak $1$ at $507$ nm) and $K_{\max} = 1700$ lm/W, the set of achievable efficacies of radiation has greatest element $1700$.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem max_luminous_efficacy_scotopic (V : ℝ → ℝ) (hV : IsLuminosityFunction V 507) :
    IsGreatest {K : ℝ | ∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ 0 < radiantFlux mu ∧
      K = efficacyOfRadiation KmScotopic V mu} 1700 := by sorry

end LuminousEfficacy
