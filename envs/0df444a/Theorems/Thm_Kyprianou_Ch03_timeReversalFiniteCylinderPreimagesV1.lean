-- Prove2me | Theorems.Thm_Kyprianou_Ch03_timeReversalFiniteCylinderPreimagesV1
-- name    : Kyprianou.Ch03.timeReversalFiniteCylinderPreimagesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:56:40.672069+00:00
-- url     : https://prove2.me/theorems/1267c650-c871-460d-b8c1-f7127daafb6e
-- title:
--   Jump-sensitive finite-cylinder probability identity
-- statement:
--   At the finitely many deterministic reflected times strictly above zero, replace left limits by values almost surely using stationarity and stochastic continuity. Sort the observation times, reverse the disjoint increment order and use independent stationary increments. Handle the terminal coordinate by X 0 = 0. This proves equality of source cylinder probabilities, independently of uncountable path-map measurability.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; exact canonical parent 738b23d9-7a4a-4950-8e30-28b1734d73dd.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.timeReversalFiniteCylinderPreimagesV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (J : Finset {s : NNReal // s <= t})
    (B : {s : NNReal // s <= t} -> Set Real)
    (hB : ∀ i ∈ J, MeasurableSet (B i)) :
    P ((fun omega : Omega =>
      fun s : {s : NNReal // s <= t} =>
        (if (s : NNReal) = t then X 0 omega
         else Function.leftLim (fun r : NNReal => X r omega) (t - (s : NNReal))) -
           X t omega) ⁻¹' Set.pi (J : Set {s : NNReal // s <= t}) B) =
    P ((fun omega : Omega => fun s : {s : NNReal // s <= t} => -(X (s : NNReal) omega)) ⁻¹' Set.pi (J : Set {s : NNReal // s <= t}) B) := by sorry
