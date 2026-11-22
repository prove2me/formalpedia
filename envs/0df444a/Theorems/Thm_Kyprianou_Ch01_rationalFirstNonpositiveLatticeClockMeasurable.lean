-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rationalFirstNonpositiveLatticeClockMeasurable
-- name    : Kyprianou.Ch01.rationalFirstNonpositiveLatticeClockMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:15:02.155491+00:00
-- url     : https://prove2.me/theorems/334ca786-7cbc-43cf-92d2-95adb1216fab
-- title:
--   The rational-time first nonpositive lattice clock is measurable
-- statement:
--   For a process with measurable deterministic-time integer-valued sections, the rational-grid first nonpositive clock is an infimum over countably many conditional rational sample times (or top). This is globally measurable into WithTop NNReal. Pathwise equality with the exact uncountable firstNonpositiveLattice under right continuity is a separate mathematical obligation for the Lamperti no-moment first-passage theorem.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4; a prerequisite for Kyprianou.Ch01.firstNonpositiveLatticeAEMeasurableFromDriver ea3122ce-4c2e-4917-9682-8ac701d400ca. Rational countable-clock mechanism follows prior Prove2Me work on ruin clocks; no finite offspring mean is needed.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rationalFirstNonpositiveLatticeClockMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    Measurable (fun ω : Ω =>
      ⨅ r : ℚ,
        if X (Real.toNNReal (r : ℝ)) ω ≤ 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤) := by
  sorry
