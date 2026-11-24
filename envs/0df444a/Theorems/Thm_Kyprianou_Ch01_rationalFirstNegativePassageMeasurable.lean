-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rationalFirstNegativePassageMeasurable
-- name    : Kyprianou.Ch01.rationalFirstNegativePassageMeasurable
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T16:58:36.082855+00:00
-- url     : https://prove2.me/theorems/f5b81f26-bf40-4a0e-912a-05607f8dcdd1
-- title:
--   Rational-grid first-negative passage clock is measurable
-- statement:
--   Assume every deterministic-time section of an integer-valued process $X$ is measurable. Form the rational-grid first strict-negative clock
--   $$\tau^{\mathbb{Q}}(\omega)=\inf\{r\in\mathbb{Q}_{>0}: X_r(\omega)<0\}$$
--   (with value $\top$ when the set is empty), realized as a countable `iInf` of `{t,\top}`-valued measurable pieces. Then $\tau^{\mathbb{Q}}$ is measurable as a map into $\overline{\mathbb{R}}_{\ge 0}$. This is the strict-negative analogue of the already proved `rationalFirstNonpositiveLatticeClockMeasurable`.
-- source:
--   Kyprianou (2006), Section 1.3.4; analogue of Prove2Me theorem Kyprianou.Ch01.rationalFirstNonpositiveLatticeClockMeasurable (334ca786-7cbc-43cf-92d2-95adb1216fab).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rationalFirstNegativePassageMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    Measurable (fun ω : Ω =>
      ⨅ r : ℚ,
        if 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤) := by
  sorry
