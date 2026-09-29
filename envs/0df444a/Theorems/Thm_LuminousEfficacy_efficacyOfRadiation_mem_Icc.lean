-- Prove2me | Theorems.Thm_LuminousEfficacy_efficacyOfRadiation_mem_Icc
-- name    : LuminousEfficacy.efficacyOfRadiation_mem_Icc
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:04:42.706595+00:00
-- url     : https://prove2.me/theorems/6875d664-af2f-48ed-a8d4-4928d3d3dd38
-- title:
--   $0 \le K \le K_{\max}$
-- statement:
--   For any source with strictly positive radiant flux, the luminous efficacy of radiation
--
--   $$K \;=\; \frac{\Phi_v}{\Phi_e}$$
--
--   lies between $0$ and the maximum spectral luminous efficacy $K_{\max}$. The hypothesis $\Phi_e > 0$ is what makes the quotient meaningful.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem efficacyOfRadiation_mem_Icc (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ) (hKmax : 0 ≤ Kmax)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) :
    efficacyOfRadiation Kmax V mu ∈ Set.Icc 0 Kmax := by sorry

end LuminousEfficacy
