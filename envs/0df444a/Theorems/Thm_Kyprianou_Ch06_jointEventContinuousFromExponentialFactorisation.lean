-- Prove2me | Theorems.Thm_Kyprianou_Ch06_jointEventContinuousFromExponentialFactorisation
-- name    : Kyprianou.Ch06.jointEventContinuousFromExponentialFactorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:59:39.985118+00:00
-- url     : https://prove2.me/theorems/39727eed-3db8-419e-be01-acf2efb5d0a8
-- title:
--   Joint probability with exponential marginal and fixed independent event is continuous in time
-- statement:
--   For an arbitrary event D under a probability measure and a family of sets f(s) whose marginal probability is exp(-rate s), if each joint event f(s)∩D has the factorisation P(f(s))P(D), then the joint probability is continuous in s. Uses continuous real exponential, ENNReal.ofReal and multiplication by the finite fixed probability P(D). This is an independently provable analytical bridge in Chapter 6 first-arrival outside-mark cylinder independence.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.jointEventContinuousFromExponentialFactorisation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : Set Omega) (rate : Real)
    (f : NNReal → Set Omega)
    (hZero : ∀ s : NNReal,
      P (f s) = ENNReal.ofReal (Real.exp (-(rate * (s : Real)))))
    (hJoint : ∀ s : NNReal,
      P ((f s) ∩ D) = P (f s) * P D)
    (t : NNReal) :
    ContinuousAt (fun s : NNReal => P ((f s) ∩ D)) t := by sorry
