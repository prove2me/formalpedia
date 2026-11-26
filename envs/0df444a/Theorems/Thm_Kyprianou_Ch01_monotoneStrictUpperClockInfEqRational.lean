-- Prove2me | Theorems.Thm_Kyprianou_Ch01_monotoneStrictUpperClockInfEqRational
-- name    : Kyprianou.Ch01.monotoneStrictUpperClockInfEqRational
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:16:01.008822+00:00
-- url     : https://prove2.me/theorems/0b275f49-c607-45b8-a477-521ceded9b4e
-- title:
--   Infimum of strict upper crossing times of any monotone ENNReal clock equals rational-grid infimum
-- statement:
--   For a monotone nondecreasing ENNReal-valued NNReal-indexed clock f and a threshold a in ENNReal, identify the infimum of the full source strict-upper-passage crossing set, mapped into WithTop NNReal, with the infimum of its rational-grid crossing times. The main proof is a direct source adaptation of the already Proved Kyprianou.Ch01.rationalFirstNonpositiveClockEqOfRightContinuous, UUID d98599a5-9b89-45f7-bc1e-63e4b82418aa. One inequality follows because each rational crossing is a source crossing. For the other, suppose a source crossing u lies strictly below the rational infimum; choose an intermediate WithTop NNReal bound v and a rational r with u < r < v. Monotonicity ensures f u ≤ f r, hence f r > a, contradicting the rational infimum being above v. No right continuity, local integrability, offspring first moment or non-explosion is needed. Handles threshold and clock infinity as order elements.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4 original reciprocalOccupation / inverseReciprocalOccupation. Exact reusable proof source Kyprianou.Ch01.rationalFirstNonpositiveClockEqOfRightContinuous, Proved UUID d98599a5-9b89-45f7-bc1e-63e4b82418aa. This is a needed child lemma of root-connected measurableInverseReciprocalOccupationFromSections UUID 2dc7607e-9030-4adc-a4f2-df34dd1edc17, itself connected via root reverse Lamperti f852e790-8678-45eb-9775-7f5af1318dd3 and original root ac1b29c6-5525-4344-a03d-7469824736ed.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.monotoneStrictUpperClockInfEqRational
    (f : ℝ≥0 → ℝ≥0∞) (hmono : Monotone f) (a : ℝ≥0∞) :
    (sInf {z : WithTop ℝ≥0 |
      ∃ u : ℝ≥0, (u : WithTop ℝ≥0) = z ∧ a < f u}) =
      ⨅ r : ℚ,
        if a < f (Real.toNNReal (r : ℝ)) then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  sorry
