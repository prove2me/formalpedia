-- Prove2me | Theorems.Thm_LuminousEfficacy_efficacyOfRadiation_dirac_peak
-- name    : LuminousEfficacy.efficacyOfRadiation_dirac_peak
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:21:33.123448+00:00
-- url     : https://prove2.me/theorems/5d56910c-ae22-42bd-941e-d3d27bdd8d13
-- title:
--   A monochromatic source at the peak wavelength attains $K_{\max}$
-- statement:
--   An ideal monochromatic source at the peak wavelength of the luminosity function - the unit point mass $\delta_{\lambda_0}$, carrying one watt at $\lambda_0$ - has radiant flux $1$ and luminous efficacy of radiation exactly $K_{\max}$:
--
--   $$\Phi_e(\delta_{\lambda_0}) = 1, \qquad K(\delta_{\lambda_0}) = K_{\max} .$$
--
--   With $\lambda_0 = 555$ nm and $K_{\max} = K_m$ this is the source's "ideal monochromatic source: 555 nm, $683.002$ lm/W, luminous efficiency $100\%$", and it supplies the attainment half of the goal theorem.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem efficacyOfRadiation_dirac_peak (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ)
    (hV : IsLuminosityFunction V peak) :
    radiantFlux (Measure.dirac peak) = 1 ∧
      efficacyOfRadiation Kmax V (Measure.dirac peak) = Kmax := by sorry

end LuminousEfficacy
