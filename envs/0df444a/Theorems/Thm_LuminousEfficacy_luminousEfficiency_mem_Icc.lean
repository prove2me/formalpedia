-- Prove2me | Theorems.Thm_LuminousEfficacy_luminousEfficiency_mem_Icc
-- name    : LuminousEfficacy.luminousEfficiency_mem_Icc
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:14:25.577988+00:00
-- url     : https://prove2.me/theorems/5d82b609-01ba-40f0-be9e-595974eac502
-- title:
--   Luminous efficiency lies in $[0,1]$
-- statement:
--   "Luminous efficacy can be normalized by the maximum possible luminous efficacy to a dimensionless quantity called luminous efficiency." This milestone states that the normalization does what the name promises: for $K_{\max} > 0$ and a source with positive radiant flux,
--
--   $$\eta \;=\; \frac{K}{K_{\max}} \;\in\; [0, 1],$$
--
--   so luminous efficiency is a genuine percentage, reaching $100\%$ exactly when the efficacy attains $K_{\max}$.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem luminousEfficiency_mem_Icc (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ) (hKmax : 0 < Kmax)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) :
    luminousEfficiency Kmax V mu ∈ Set.Icc 0 1 := by sorry

end LuminousEfficacy
