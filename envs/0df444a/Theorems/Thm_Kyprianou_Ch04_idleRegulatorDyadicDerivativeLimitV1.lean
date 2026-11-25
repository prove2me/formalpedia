-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorDyadicDerivativeLimitV1
-- name    : Kyprianou.Ch04.idleRegulatorDyadicDerivativeLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:33:45.136014+00:00
-- url     : https://prove2.me/theorems/d1f4eac2-3d23-4757-86f0-afccc425d48b
-- title:
--   Dyadic right difference quotients converge to the derivative
-- statement:
--   For a differentiable time-extended regulator, the positive dyadic step tends to zero and its difference quotients converge to the derivative. Restrict the derivative limit to the dyadic sequence, using the nonnegative-time addition identity.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic derivative calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleRegulatorDyadicDerivativeLimitV1
    (R : NNReal → Real) (t : Real) (ht0 : 0 ≤ t)
    (hdiff : DifferentiableAt Real (fun s : Real => R s.toNNReal) t) :
    let delta : Nat → NNReal := fun n => ((1 : NNReal) / 2) ^ n
    (∀ n, 0 < (delta n : Real)) ∧
    Tendsto (fun n => (delta n : Real)) atTop (𝓝 0) ∧
    Tendsto (fun n => (R (t.toNNReal + delta n) - R t.toNNReal) / (delta n : Real))
      atTop (𝓝 (deriv (fun s : Real => R s.toNNReal) t)) := by
  sorry
