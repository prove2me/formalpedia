-- Prove2me | Theorems.Thm_Kyprianou_Ch06_independentAtomlessRealFirstArrivalTieNull
-- name    : Kyprianou.Ch06.independentAtomlessRealFirstArrivalTieNull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:28:01.526939+00:00
-- url     : https://prove2.me/theorems/164c0b78-3fd7-4c45-af68-2f29782cd337
-- title:
--   Lemma 6.18: independent real-valued atomless arrival times almost surely never tie
-- statement:
--   For two independent measurable real-valued random variables, if the second has an atomless distribution, the probability that their values coincide is zero. No identical-law assumption is needed. This is the probabilistic no-tie theorem necessary for competing marked Poisson first-arrival times of different intensities.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, uniqueness of the competing first marked Poisson arrival; pinned Mathlib product measure/Fubini independence.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.independentAtomlessRealFirstArrivalTieNull
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f g : Omega → Real) (hf : Measurable f) (hg : Measurable g)
    (hIndep : ProbabilityTheory.IndepFun f g P)
    (hNoAtoms : ∀ x : Real, (Measure.map g P) {x} = 0) :
    P {omega | f omega = g omega} = 0 := by sorry
