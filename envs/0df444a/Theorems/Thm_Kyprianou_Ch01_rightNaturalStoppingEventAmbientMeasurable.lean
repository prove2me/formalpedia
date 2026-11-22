-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingEventAmbientMeasurable
-- name    : Kyprianou.Ch01.rightNaturalStoppingEventAmbientMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:51:38.516432+00:00
-- url     : https://prove2.me/theorems/05a1843f-044c-4ca5-ade8-610462ac7484
-- title:
--   A right-natural stopping-time lower set is measurable in the ambient sigma-field
-- statement:
--   Every event {tau≤t} for a stopping time in the right-continuous natural filtration is measurable in the ambient sample-space sigma-field whenever all fixed-time coordinates X(t) are measurable. This is immediate from the exact definition of right-natural stopping time and the proved sigma-field embedding naturalSigmaRight_le_ambient, but is a useful bridge for optional sampling and stopped-process measurability.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13, measurability of stopping-time events.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rightNaturalStoppingEventAmbientMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsNaturalRightStoppingTime X τ)
    (t : ℝ≥0) :
    MeasurableSet {ω : Ω | τ ω ≤ (t : WithTop ℝ≥0)} := by sorry
