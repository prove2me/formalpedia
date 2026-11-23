-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroStageReciprocalOccupationTop
-- name    : Kyprianou.Ch01.reverseLampertiZeroStageReciprocalOccupationTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:39:25.081382+00:00
-- url     : https://prove2.me/theorems/cf1e379f-44e5-4500-8a4f-c758b3b6eb10
-- title:
--   Reciprocal occupation diverges across a positive-length zero-population interval
-- statement:
--   If an integer-valued driving path is exactly zero on a nondegenerate physical-time interval (a,s), with 0≤a<s, its reciprocal occupation integral from zero to s is infinite. The integrand equals the ENNReal infinity on a set of strictly positive Lebesgue measure. This source-faithful analytic lemma resolves the zero-stage component of reverse Lamperti inverse clock at extinction; it does not assert a stochastic Markov property or any separate regularity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiZeroStageReciprocalOccupationTop
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (a s : ℝ) (ha : 0 ≤ a) (has : a < s)
    (hZero : ∀ u : ℝ≥0,
      a < (u : ℝ) → (u : ℝ) < s → X u ω = 0) :
    reciprocalOccupation X (Real.toNNReal s) ω = ⊤ := by
  sorry
