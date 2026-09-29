-- Prove2me | Theorems.Thm_LuminousEfficacy_max_luminous_efficacy_photopic
-- name    : LuminousEfficacy.max_luminous_efficacy_photopic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:42:48.07841+00:00
-- url     : https://prove2.me/theorems/054967b9-1a7f-4f57-9419-b728aef14405
-- title:
--   Maximum possible photopic luminous efficacy of radiation is $683.002\ \mathrm{lm/W}$
-- statement:
--   **Goal theorem.** *Photopic luminous efficacy of radiation has a maximum possible value of $683.002$ lm/W, for the case of monochromatic light at a wavelength of $555$ nm.*
--
--   Fix any photopic luminosity function $V$, i.e. a measurable $V : \mathbb{R} \to \mathbb{R}$ with $0 \le V \le 1$ and $V(555) = 1$. Consider the set of achievable luminous efficacies of radiation
--
--   $$\mathcal{K} \;=\; \Big\{\, K_m \tfrac{\int V \,\mathrm{d}\mu}{\mu(\mathbb{R})} \;:\; \mu \text{ a finite spectral radiant flux distribution with } \mu(\mathbb{R}) > 0 \,\Big\}, \qquad K_m = 683.002 .$$
--
--   Then $683.002$ is the **greatest** element of $\mathcal{K}$: every source has $K \le 683.002$ lm/W, and the value is attained, by the monochromatic source at $555$ nm (the unit point mass at $555$).
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Definitions.Def_luminous_efficacy
open MeasureTheory

namespace LuminousEfficacy

theorem max_luminous_efficacy_photopic (V : ℝ → ℝ) (hV : IsLuminosityFunction V 555) :
    IsGreatest {K : ℝ | ∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ 0 < radiantFlux mu ∧
      K = efficacyOfRadiation Km V mu} 683.002 := by sorry

end LuminousEfficacy
