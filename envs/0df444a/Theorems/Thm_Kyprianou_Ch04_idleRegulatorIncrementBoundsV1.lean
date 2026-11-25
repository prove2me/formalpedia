-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorIncrementBoundsV1
-- name    : Kyprianou.Ch04.idleRegulatorIncrementBoundsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:15:39.978801+00:00
-- url     : https://prove2.me/theorems/61e4aea7-1edb-413e-99b0-bf583735c300
-- title:
--   Deterministic positive drift bounds for the idle regulator
-- statement:
--   A path starting at zero and with increments bounded above by the linear drift has a monotone d-Lipschitz capped running supremum. More sharply, a new record over (s,t] must come from a value bounded by f(s)+d(t-s). Thus the regulator increment is bounded above by the positive part of this quantity minus its value at s. This controls the zero-workload and nonzero-workload cases simultaneously.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic regulator calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleRegulatorIncrementBoundsV1
    (f : NNReal → Real) (d w : Real) (hd : 0 < d) (hw : 0 ≤ w)
    (hf0 : f 0 = 0)
    (hf : ∀ s t : NNReal, s ≤ t →
      f t - f s ≤ d * ((t : Real) - (s : Real))) :
    let R : NNReal → Real := fun t => max w (sSup (f '' Iic t))
    R 0 = w ∧
    (∀ t, f t ≤ R t) ∧
    (∀ s t : NNReal, s ≤ t →
      0 ≤ R t - R s ∧
      R t - R s ≤ max 0 (f s - R s + d * ((t : Real) - (s : Real)))) ∧
    LipschitzWith (Real.toNNReal d) R := by
  sorry
