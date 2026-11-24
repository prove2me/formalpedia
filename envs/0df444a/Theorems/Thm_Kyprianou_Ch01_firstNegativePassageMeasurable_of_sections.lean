-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassageMeasurable_of_sections
-- name    : Kyprianou.Ch01.firstNegativePassageMeasurable_of_sections
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:56:29.287401+00:00
-- url     : https://prove2.me/theorems/0879eed9-172e-46c8-83ec-f680b83ed0cf
-- title:
--   First-negative passage measurable from measurable time-sections
-- statement:
--   Assume every deterministic-time section of an integer-valued process $X$ is measurable. Prove that the first strict-negative passage
--   $$\tau_0^-(\omega)=\inf\{t>0:X_t(\omega)<0\}\in\overline{\mathbb{R}}_{\ge0}$$
--   is a measurable function of the sample point. This isolates the analytic content of `firstNegativePassageMeasurable` after joint product measurability has been reduced to sections.
-- source:
--   Kyprianou (2006), Section 1.3.4; corrected reduction target after disproof of rational identification without path regularity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassageMeasurable_of_sections
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  sorry
