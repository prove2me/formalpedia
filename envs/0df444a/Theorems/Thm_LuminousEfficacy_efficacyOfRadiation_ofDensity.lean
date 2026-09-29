-- Prove2me | Theorems.Thm_LuminousEfficacy_efficacyOfRadiation_ofDensity
-- name    : LuminousEfficacy.efficacyOfRadiation_ofDensity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:28:31.514451+00:00
-- url     : https://prove2.me/theorems/cd22a3a6-3492-44ee-aab0-3273dffc6c06
-- title:
--   Integral formula for a spectrum given by a spectral radiant flux density
-- statement:
--   This milestone reconciles the measure-theoretic model with the displayed formula of the source. If the spectral radiant flux distribution has a density $\Phi_{e,\lambda}$ (measurable, nonnegative, integrable, with positive total), then
--
--   $$\Phi_e = \int \Phi_{e,\lambda}\, \mathrm{d}\lambda, \qquad K = \frac{K_{\max}\int V(\lambda)\,\Phi_{e,\lambda}\,\mathrm{d}\lambda}{\int \Phi_{e,\lambda}\,\mathrm{d}\lambda},$$
--
--   which is exactly the source's definition $K = \Phi_v / \Phi_e$ with $\Phi_v = \int K(\lambda)\Phi_{e,\lambda}\,\mathrm{d}\lambda$ and $K(\lambda) = K_m V(\lambda)$.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem efficacyOfRadiation_ofDensity (Kmax : ℝ) (V Phi : ℝ → ℝ) (peak : ℝ)
    (hV : IsLuminosityFunction V peak) (hPhimeas : Measurable Phi) (hPhinonneg : ∀ l, 0 ≤ Phi l)
    (hPhiint : Integrable Phi) (hPhipos : 0 < ∫ l, Phi l) :
    radiantFlux (ofDensity Phi) = ∫ l, Phi l ∧
      efficacyOfRadiation Kmax V (ofDensity Phi)
        = (Kmax * ∫ l, V l * Phi l) / ∫ l, Phi l := by sorry

end LuminousEfficacy
