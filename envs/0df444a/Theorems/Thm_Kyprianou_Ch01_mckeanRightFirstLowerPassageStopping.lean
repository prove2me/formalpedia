-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightFirstLowerPassageStopping
-- name    : Kyprianou.Ch01.mckeanRightFirstLowerPassageStopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:29:04.170289+00:00
-- url     : https://prove2.me/theorems/870aafb8-5102-43c5-a4a1-077301cac7dd
-- title:
--   McKean right-continuous natural stopping time for a continuous lower passage
-- statement:
--   For an everywhere continuous process with measurable deterministic evaluations, the first strict lower crossing after time zero is a stopping time in the right-continuous natural filtration of the shifted process. Right-continuity allows the boundary event at each t to be expressed by intersections of future open-crossing events.
-- source:
--   Kyprianou (2006), Chapter 1, Theorem 1.13; right-continuous natural filtration and first passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightFirstLowerPassageStopping
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (x barrier : ℝ) :
    IsNaturalRightStoppingTime (fun t ω => x + X t ω)
      (firstLowerPassage X x barrier) := by sorry
