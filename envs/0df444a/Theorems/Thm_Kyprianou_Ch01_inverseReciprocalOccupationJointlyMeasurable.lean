-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationJointlyMeasurable
-- name    : Kyprianou.Ch01.inverseReciprocalOccupationJointlyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T14:19:43.802368+00:00
-- url     : https://prove2.me/theorems/1c590987-c68c-48f8-bd2c-5ddefffd6958
-- title:
--   Inverse reciprocal occupation is jointly measurable
-- statement:
--   Let $X$ be an integer-valued path that is jointly measurable in calendar time and the sample point. Then the inverse reciprocal-occupation clock $\theta_t(\omega)\in\overline{\mathbb{R}}_{\ge 0}$ is jointly measurable in $(t,\omega)$.
-- source:
--   Kyprianou (2006), Section 1.3.4; measurability of the Lamperti inverse occupation clock.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseReciprocalOccupationJointlyMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable
      (fun p : Ω × ℝ≥0 => inverseReciprocalOccupation X p.2 p.1) := by
  sorry
