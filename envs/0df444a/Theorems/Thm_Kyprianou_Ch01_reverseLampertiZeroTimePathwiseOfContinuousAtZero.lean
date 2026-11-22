-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroTimePathwiseOfContinuousAtZero
-- name    : Kyprianou.Ch01.reverseLampertiZeroTimePathwiseOfContinuousAtZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:38:37.376105+00:00
-- url     : https://prove2.me/theorems/87b14b80-3020-4438-9015-747d7444a3c7
-- title:
--   Zero-time inverse Lamperti state recovery for a nonnegative integer right-continuous path
-- statement:
--   For an integer-valued path that is right-continuous at zero and starts nonnegative, the reciprocal-occupation clock immediately crosses zero. Its generalised inverse at level zero is zero, and the strict-negative-passage stop does not precede zero. Consequently the reverse Lamperti state at time zero agrees with the input path at zero. Both zero and positive starting populations are included.
-- source:
--   Kyprianou (2006), Chapter 1, inverse Lamperti construction, equation (1.19); deterministic pathwise lemma

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiZeroTimePathwiseOfContinuousAtZero
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hNonneg : 0 ≤ X 0 ω)
    (hRight : ContinuousWithinAt
      (fun s : ℝ≥0 => X s ω) (Set.Ici 0) 0) :
    (compoundPoissonToBranching X 0 ω).toNat = (X 0 ω).toNat := by
  sorry
