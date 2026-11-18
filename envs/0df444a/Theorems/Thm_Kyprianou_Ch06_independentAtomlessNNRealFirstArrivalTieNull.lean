-- Prove2me | Theorems.Thm_Kyprianou_Ch06_independentAtomlessNNRealFirstArrivalTieNull
-- name    : Kyprianou.Ch06.independentAtomlessNNRealFirstArrivalTieNull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:10:31.704978+00:00
-- url     : https://prove2.me/theorems/3d430968-9186-4830-988c-9fd2df662a65
-- title:
--   Lemma 6.18: two independent atomless NNReal arrival times have zero probability of tying
-- statement:
--   Two independent measurable nonnegative real-valued random arrival times cannot coincide with positive probability if one has an atomless distribution. This extends the independently Proved Real-valued diagonal-product measure argument directly to nonnegative first-arrival times in the Kyprianou marked Poisson model.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, uniqueness of the first mark among competing positive-rate Poisson arrivals.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.independentAtomlessNNRealFirstArrivalTieNull
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f g : Omega → NNReal) (hf : Measurable f) (hg : Measurable g)
    (hIndep : ProbabilityTheory.IndepFun f g P)
    (hNoAtoms : ∀ x : NNReal, (Measure.map g P) {x} = 0) :
    P {omega | f omega = g omega} = 0 := by sorry
