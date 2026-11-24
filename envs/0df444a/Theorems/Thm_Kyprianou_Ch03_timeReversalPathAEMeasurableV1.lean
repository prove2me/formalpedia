-- Prove2me | Theorems.Thm_Kyprianou_Ch03_timeReversalPathAEMeasurableV1
-- name    : Kyprianou.Ch03.timeReversalPathAEMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:56:41.327299+00:00
-- url     : https://prove2.me/theorems/42196240-b3a8-4082-98f6-d9e7e4a02b71
-- title:
--   Almost-everywhere measurable forward and left-limit reversed paths
-- statement:
--   Establish almost-everywhere measurability into the product measurable space over the entire time interval. Use the common almost-sure cadlag event and countable deterministic rational approximations to construct simultaneous measurable versions; coordinatewise a.e. measurability alone does not suffice for an uncountable index.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; exact canonical parent 738b23d9-7a4a-4950-8e30-28b1734d73dd.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.timeReversalPathAEMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t) :
    AEMeasurable (fun omega : Omega =>
      fun s : {s : NNReal // s <= t} =>
        (if (s : NNReal) = t then X 0 omega
         else Function.leftLim (fun r : NNReal => X r omega) (t - (s : NNReal))) -
           X t omega) P ∧
    AEMeasurable (fun omega : Omega => fun s : {s : NNReal // s <= t} => -(X (s : NNReal) omega)) P := by sorry
