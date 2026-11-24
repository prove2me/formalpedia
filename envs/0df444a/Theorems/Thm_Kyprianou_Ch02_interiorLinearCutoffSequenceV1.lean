-- Prove2me | Theorems.Thm_Kyprianou_Ch02_interiorLinearCutoffSequenceV1
-- name    : Kyprianou.Ch02.interiorLinearCutoffSequenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:03:06.427807+00:00
-- url     : https://prove2.me/theorems/6e9eea61-7890-40fb-9320-6e13125ede46
-- title:
--   Bounded continuous cutoffs approximate the interior linear jump mark
-- statement:
--   Use f_n(x)=min(max(0,x-1/(n+1)), max(0,(n+1)(r-x))). These functions are bounded, vanish near zero and outside (0,r), and converge pointwise to the interior linear mark.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, small-time moment and drift characterisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.interiorLinearCutoffSequenceV1
    (r : ℝ) (hr : 0 < r) :
    ∃ f : ℕ → BoundedContinuousFunction ℝ ℝ,
      (∀ n x, 0 ≤ f n x) ∧
      (∀ n x, f n x ≤ (Set.Ioo (0 : ℝ) r).indicator id x) ∧
      (∀ n, ∃ δ > 0, ∀ x, |x| < δ → f n x = 0) ∧
      ∀ x, Tendsto (fun n => f n x) atTop
        (nhds ((Set.Ioo (0 : ℝ) r).indicator id x)) := by
  sorry
