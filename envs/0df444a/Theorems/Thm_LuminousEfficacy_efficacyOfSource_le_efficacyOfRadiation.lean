-- Prove2me | Theorems.Thm_LuminousEfficacy_efficacyOfSource_le_efficacyOfRadiation
-- name    : LuminousEfficacy.efficacyOfSource_le_efficacyOfRadiation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:33:11.146654+00:00
-- url     : https://prove2.me/theorems/9004f2cf-b5d0-4fe5-878c-c82d1bcb4899
-- title:
--   Overall luminous efficacy never exceeds the efficacy of radiation
-- statement:
--   "The main difference between the luminous efficacy of radiation and the luminous efficacy of a source is that the latter accounts for input energy that is lost as heat or otherwise exits the source as something other than electromagnetic radiation." Formally, if the input power $P$ is at least the radiant flux $\Phi_e > 0$, then
--
--   $$\frac{\Phi_v}{P} \;\le\; \frac{\Phi_v}{\Phi_e} \;\le\; K_{\max},$$
--
--   so the overall (wall-plug) luminous efficacy is bounded by the efficacy of radiation, and hence by the same ceiling $K_{\max}$.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem efficacyOfSource_le_efficacyOfRadiation (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ)
    (hKmax : 0 ≤ Kmax) (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) (P : ℝ) (hP : radiantFlux mu ≤ P) :
    efficacyOfSource Kmax V mu P ≤ efficacyOfRadiation Kmax V mu ∧
      efficacyOfSource Kmax V mu P ≤ Kmax := by sorry

end LuminousEfficacy
