-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiStoppedClockMeasurable
-- name    : Kyprianou.Ch01.lampertiStoppedClockMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:25:36.38317+00:00
-- url     : https://prove2.me/theorems/88baaa7b-c3f5-4363-8c5a-9208ad69b557
-- title:
--   Lamperti stopped clock is jointly measurable
-- statement:
--   Let $X$ be an integer-valued path that is jointly measurable in calendar time and the sample point. Then the stopped Lamperti clock $\min(\theta_t,\tau_0^-)$ — the minimum of the inverse reciprocal-occupation time and the first strict negative passage — is a jointly measurable $\overline{\mathbb{R}}_{\ge 0}$-valued map of $(t,\omega)$.
-- source:
--   Kyprianou (2006), Section 1.3.4; measurability of the reverse Lamperti time change.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiStoppedClockMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable
      (fun p : Ω × ℝ≥0 =>
        min (inverseReciprocalOccupation X p.2 p.1)
          (firstNegativePassage X p.1)) := by
  sorry
