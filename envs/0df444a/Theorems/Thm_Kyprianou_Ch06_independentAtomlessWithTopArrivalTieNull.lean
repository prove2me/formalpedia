-- Prove2me | Theorems.Thm_Kyprianou_Ch06_independentAtomlessWithTopArrivalTieNull
-- name    : Kyprianou.Ch06.independentAtomlessWithTopArrivalTieNull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:13:14.430101+00:00
-- url     : https://prove2.me/theorems/d3533426-a587-46b6-b016-487887eb47b2
-- title:
--   Lemma 6.18: independent atomless extended nonnegative first-arrival clocks almost surely never tie
-- statement:
--   Two independent measurable random variables with values in WithTop NNReal, representing arrival times possibly equal to infinity, have zero probability of coinciding if one marginal law is atomless, including at infinity. This directly supports the competing first-mark clocks used in the Chapter 6 first-mark probability identity.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, competing first marked-Poisson arrivals have almost surely distinct finite times under two positive intensities.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.independentAtomlessWithTopArrivalTieNull
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f g : Omega → WithTop NNReal) (hf : Measurable f) (hg : Measurable g)
    (hIndep : ProbabilityTheory.IndepFun f g P)
    (hNoAtoms : ∀ x : WithTop NNReal, (Measure.map g P) {x} = 0) :
    P {omega | f omega = g omega} = 0 := by sorry
