-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorIncrementCoreV1
-- name    : Kyprianou.Ch04.idleRegulatorIncrementCoreV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:25:04.726813+00:00
-- url     : https://prove2.me/theorems/72b446ad-9856-42c0-8f74-7f2dd8b8800c
-- title:
--   Sharp increment bounds for the capped running maximum
-- statement:
--   Use boundedness of the finite path range under the increment bound. Separate old records from values in the new time interval; these latter values are at most f(s)+d(t-s).
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic regulator calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleRegulatorIncrementCoreV1
    (f : NNReal → Real) (d w : Real) (hd : 0 < d) (hw : 0 ≤ w)
    (hf0 : f 0 = 0)
    (hf : ∀ s t : NNReal, s ≤ t →
      f t - f s ≤ d * ((t : Real) - (s : Real))) :
    let R : NNReal → Real := fun t => max w (sSup (f '' Iic t))
    R 0 = w ∧
    (∀ t, f t ≤ R t) ∧
    (∀ s t : NNReal, s ≤ t →
      0 ≤ R t - R s ∧
      R t - R s ≤ max 0 (f s - R s + d * ((t : Real) - (s : Real)))) := by
  sorry
