-- Prove2me | Theorems.Thm_LuminousEfficacy_efficacyOfRadiation_smul
-- name    : LuminousEfficacy.efficacyOfRadiation_smul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:30:07.319453+00:00
-- url     : https://prove2.me/theorems/8fd42f89-58ac-4846-aeee-aea3fc42e12f
-- title:
--   Luminous efficacy of radiation is intensive (scale-invariant)
-- statement:
--   Luminous efficacy of radiation is a ratio and therefore a property of the *spectrum*, not of the size of the source: brightening a source by a factor $c > 0$ without changing its spectral shape leaves $K$ unchanged,
--
--   $$K(c\mu) = K(\mu).$$
--
--   This is why the tabulated efficacies of the source depend only on the type of emitter (a $2800$ K black body, a class M star) and not on its wattage.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem efficacyOfRadiation_smul (Kmax : ℝ) (V : ℝ → ℝ) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) (c : ENNReal) (hc : c ≠ 0) (hctop : c ≠ ⊤) :
    efficacyOfRadiation Kmax V (c • mu) = efficacyOfRadiation Kmax V mu := by sorry

end LuminousEfficacy
