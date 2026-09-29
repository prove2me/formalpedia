-- Prove2me | Theorems.Thm_LuminousEfficacy_luminousFlux_nonneg
-- name    : LuminousEfficacy.luminousFlux_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:44:40.478632+00:00
-- url     : https://prove2.me/theorems/fce60caa-ebe1-453f-8f16-4ca076a2ecb5
-- title:
--   Luminous flux is nonnegative
-- statement:
--   For a nonnegative maximum spectral luminous efficacy $K_{\max} \ge 0$, a luminosity function $V$ (values in $[0,1]$, peak $1$ at some wavelength), and an arbitrary spectral radiant flux distribution $\mu$, the luminous flux
--
--   $$\Phi_v = K_{\max} \int V \,\mathrm{d}\mu$$
--
--   is nonnegative: no part of the spectrum subtracts luminous flux.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem luminousFlux_nonneg (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ) (hKmax : 0 ≤ Kmax)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) :
    0 ≤ luminousFlux Kmax V mu := by sorry

end LuminousEfficacy
