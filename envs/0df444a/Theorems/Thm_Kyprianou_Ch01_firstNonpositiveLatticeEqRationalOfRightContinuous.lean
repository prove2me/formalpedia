-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNonpositiveLatticeEqRationalOfRightContinuous
-- name    : Kyprianou.Ch01.firstNonpositiveLatticeEqRationalOfRightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:23:36.856514+00:00
-- url     : https://prove2.me/theorems/63f8b2f6-625b-42e0-9e2a-c94f66721b02
-- title:
--   The original firstNonpositiveLattice clock equals its rational-time clock for right-continuous paths
-- statement:
--   For an integer-valued right-continuous path indexed by nonnegative real times, the precise Kyprianou.Ch01.firstNonpositiveLattice definition, which returns a WithTop NNReal coercion of the nonempty NNReal hitting-set infimum and top when no hit exists, equals the rational-sample clock using the infimum over rational times. Use the already Proved rationalFirstNonpositiveClockEqOfRightContinuous theorem and identify the source NNReal-infimum/coercion with the WithTop infimum of the image of the hitting set via WithTop.coe_sInf'. This handles time zero and never-hit cases, and is the precise source-level bridge needed to prove the original first-passage random clock almost everywhere measurable.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4, original source exact firstNonpositiveLattice definition. Requires public Proved Kyprianou.Ch01.rationalFirstNonpositiveClockEqOfRightContinuous UUID d98599a5-9b89-45f7-bc1e-63e4b82418aa and Mathlib WithTop.coe_sInf'. Supports open driver first-hit theorem ea3122ce-4c2e-4917-9682-8ac701d400ca.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNonpositiveLatticeEqRationalOfRightContinuous
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hright : ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t) :
    firstNonpositiveLattice X ω =
      ⨅ r : ℚ,
        if X (Real.toNNReal (r : ℝ)) ω ≤ 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  sorry
