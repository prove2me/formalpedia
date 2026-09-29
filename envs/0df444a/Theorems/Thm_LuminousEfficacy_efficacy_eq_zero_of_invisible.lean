-- Prove2me | Theorems.Thm_LuminousEfficacy_efficacy_eq_zero_of_invisible
-- name    : LuminousEfficacy.efficacy_eq_zero_of_invisible
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:34:05.049342+00:00
-- url     : https://prove2.me/theorems/87d73efa-fb22-4605-8fcf-0cc86fa6495d
-- title:
--   Radiation outside the visible band produces no light
-- statement:
--   "By definition, light outside the visible spectrum cannot be seen by the standard human vision system, and therefore does not contribute to luminous efficacy." If a source radiates only at wavelengths where the luminosity function vanishes - a pure infrared or ultraviolet emitter - then its luminous flux and its luminous efficacy of radiation are both zero, however large its radiant flux.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem efficacy_eq_zero_of_invisible (Kmax : ℝ) (V : ℝ → ℝ) (mu : Measure ℝ)
    (hV : ∀ᵐ l ∂mu, V l = 0) :
    luminousFlux Kmax V mu = 0 ∧ efficacyOfRadiation Kmax V mu = 0 := by sorry

end LuminousEfficacy
