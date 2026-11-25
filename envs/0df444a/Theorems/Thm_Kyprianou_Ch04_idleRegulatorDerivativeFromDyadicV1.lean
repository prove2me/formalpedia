-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorDerivativeFromDyadicV1
-- name    : Kyprianou.Ch04.idleRegulatorDerivativeFromDyadicV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:15:40.740912+00:00
-- url     : https://prove2.me/theorems/72aa7880-940b-460a-9e95-3e15fadbc1bd
-- title:
--   Derivative of the Lipschitz idle regulator at positive times
-- statement:
--   Extend the regulator to real time by toNNReal; its Lipschitz property implies differentiability almost everywhere. The dyadic right slopes of the regulator at contact converge to d by squeezing between the path slope and d. Away from contact, the increment bound forces the regulator to be constant for sufficiently small positive steps. Uniqueness of the derivative identifies it with d times the idle indicator.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic regulator calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleRegulatorDerivativeFromDyadicV1
    (f R : NNReal → Real) (d : Real) (hd : 0 < d)
    (hdom : ∀ t, f t ≤ R t)
    (hinc : ∀ s t : NNReal, s ≤ t →
      0 ≤ R t - R s ∧
      R t - R s ≤ max 0 (f s - R s + d * ((t : Real) - (s : Real))))
    (hLip : LipschitzWith (Real.toNNReal d) R)
    (hSlope : ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      Tendsto (fun n : Nat =>
        (d * ((((1 : NNReal) / 2) ^ n : NNReal) : Real) -
          (f (Real.toNNReal t + ((1 : NNReal) / 2) ^ n) -
            f (Real.toNNReal t))) /
          ((((1 : NNReal) / 2) ^ n : NNReal) : Real))
        atTop (𝓝 (0 : Real))) :
    ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      deriv (fun s : Real => R (Real.toNNReal s)) t =
        if R (Real.toNNReal t) - f (Real.toNNReal t) = 0 then d else 0 := by
  sorry
