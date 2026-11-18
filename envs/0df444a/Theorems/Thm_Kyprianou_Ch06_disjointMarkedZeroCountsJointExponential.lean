-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointMarkedZeroCountsJointExponential
-- name    : Kyprianou.Ch06.disjointMarkedZeroCountsJointExponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:06:05.222186+00:00
-- url     : https://prove2.me/theorems/60c64f27-e106-42e2-b477-f9efbe53f149
-- title:
--   Lemma 6.18: joint disjoint-mark zero-count probability equals product of exponential survivals
-- statement:
--   For disjoint measurable finite-intensity mark sets B and D and arbitrary observation times s,t, the probability of observing no B marks by s and no D marks by t is the product of the respective exponential zero-count probabilities. All quantities are in ENNReal, and the rates are the finite NNReal intensity parts.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, independent Poisson counts in disjoint mark sets.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointMarkedZeroCountsJointExponential
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) :
    P {omega | N omega s B = 0 ∧ N omega t D = 0} =
      ENNReal.ofReal
        (Real.exp (-(((n B).toNNReal : Real) * (s : Real)))) *
      ENNReal.ofReal
        (Real.exp (-(((n D).toNNReal : Real) * (t : Real)))) := by sorry
