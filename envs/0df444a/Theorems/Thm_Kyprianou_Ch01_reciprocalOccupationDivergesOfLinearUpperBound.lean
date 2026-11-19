-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationDivergesOfLinearUpperBound
-- name    : Kyprianou.Ch01.reciprocalOccupationDivergesOfLinearUpperBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:36:00.429829+00:00
-- url     : https://prove2.me/theorems/8f962986-a5ba-422c-85a6-208c62ebd06d
-- title:
--   Chapter 1: deterministic reciprocal-occupation divergence under linear upper growth
-- statement:
--   For a real-time integer-valued path whose values have a positive finite linear upper bound, the extended reciprocal-speed occupation clock exceeds any finite branching time at some physical time. At non-positive states its inverse ENNReal integrand is infinite. Otherwise comparison with the reciprocal of the linear bound gives an unbounded logarithmic integral.
-- source:
--   Protter-style deterministic inverse-speed time changes and Kyprianou (2006), Chapter 1 section 1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationDivergesOfLinearUpperBound
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (C : ℝ) (hC : 0 < C)
    (hUpper : ∀ t : ℝ≥0,
      (X t ω : ℝ) ≤ C * (1 + (t : ℝ))) :
    ∀ t : ℝ≥0, ∃ s : ℝ≥0,
      (t : ℝ≥0∞) < reciprocalOccupation X s ω := by
  sorry
