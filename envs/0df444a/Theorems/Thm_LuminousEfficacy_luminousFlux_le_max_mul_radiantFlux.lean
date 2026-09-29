-- Prove2me | Theorems.Thm_LuminousEfficacy_luminousFlux_le_max_mul_radiantFlux
-- name    : LuminousEfficacy.luminousFlux_le_max_mul_radiantFlux
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:49:32.351095+00:00
-- url     : https://prove2.me/theorems/089542eb-d52b-4b3c-931c-01ec3cd0036b
-- title:
--   $\Phi_v \le K_{\max} \Phi_e$
-- statement:
--   The core inequality of the mission: since the luminosity function never exceeds its peak value $1$, the luminous flux of a finite spectral radiant flux distribution $\mu$ satisfies
--
--   $$\Phi_v \;=\; K_{\max} \int V \,\mathrm{d}\mu \;\le\; K_{\max}\, \mu(\mathbb{R}) \;=\; K_{\max} \Phi_e .$$
--
--   Radiation at wavelengths where the eye is less sensitive contributes to $\Phi_e$ while contributing less than $K_{\max}$ per watt to $\Phi_v$.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem luminousFlux_le_max_mul_radiantFlux (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ) (hKmax : 0 ≤ Kmax)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    luminousFlux Kmax V mu ≤ Kmax * radiantFlux mu := by sorry

end LuminousEfficacy
