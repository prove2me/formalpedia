-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawReversalFiniteCylinderV1
-- name    : Kyprianou.Ch03.rawReversalFiniteCylinderV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:06:58.988834+00:00
-- url     : https://prove2.me/theorems/8ac9ed28-eeeb-4802-8031-7ce3fe9b88b5
-- title:
--   Finite cylinder laws for ordinary deterministic-time reversal
-- statement:
--   Sort the finite observation times, inserting zero. The disjoint increment vector on the forward partition has the same joint law as the reverse-order reflected increment vector, by independent increments and equality of each lag. Apply the negative cumulative-sum map, then the coordinate restrictions. This is the deterministic-time part of the duality argument.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4, exact parent 738b23d9-7a4a-4950-8e30-28b1734d73dd and children 42196240-b3a8-4082-98f6-d9e7e4a02b71, 1267c650-c871-460d-b8c1-f7127daafb6e.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.rawReversalFiniteCylinderV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (J : Finset {s : NNReal // s <= t})
    (B : {s : NNReal // s <= t} -> Set Real)
    (hB : ∀ i ∈ J, MeasurableSet (B i)) :
    P ((fun omega : Omega => fun s : {s : NNReal // s <= t} =>
      X (t - (s : NNReal)) omega - X t omega) ⁻¹'
        Set.pi (J : Set {s : NNReal // s <= t}) B) =
    P ((fun omega : Omega => fun s : {s : NNReal // s <= t} =>
      -(X (s : NNReal) omega)) ⁻¹'
        Set.pi (J : Set {s : NNReal // s <= t}) B) := by sorry
