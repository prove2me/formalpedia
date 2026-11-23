-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedInverseReciprocalOccupation
-- name    : Kyprianou.Ch01.reverseLampertiShiftedInverseReciprocalOccupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:15:14.208937+00:00
-- url     : https://prove2.me/theorems/1e0d9d0f-afe2-4196-99f9-14cafb4a4b47
-- title:
--   Inverse reciprocal-occupation clock shifts across a positive constant prefix
-- statement:
--   Prove the reciprocal-occupation integral splits over the positive constant prefix and the translated tail. Then transfer the strict superlevel sInf through this additive identity. Boundary case t=A/y requires the shifted tail inverse clock at time zero to be zero.
-- source:
--   Kyprianou (2006) Section 1.3.4, exact deterministic first-arrival clock shift; source-bound sublemma of the corrected stopped-clock identity 0de88083-a67c-4b90-9805-533ccf713df7.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiShiftedInverseReciprocalOccupation
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    inverseReciprocalOccupation X t ω =
      (((Real.toNNReal A : ℝ≥0) : WithTop ℝ≥0) +
        inverseReciprocalOccupation Y
          (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω) := by
  sorry
