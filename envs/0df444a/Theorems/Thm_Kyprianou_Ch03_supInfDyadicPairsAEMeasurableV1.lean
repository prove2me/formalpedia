-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDyadicPairsAEMeasurableV1
-- name    : Kyprianou.Ch03.supInfDyadicPairsAEMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T10:08:42.668636+00:00
-- url     : https://prove2.me/theorems/611aefc4-8b6f-4996-87d9-9cc7a33406e8
-- title:
--   Almost-everywhere measurability of finite dyadic extrema pairs
-- statement:
--   All deterministic-time coordinates are almost-everywhere measurable. Finite suprema and infima are measurable functions of the finite vector; use the coordinate product theorem and measurable arithmetic.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; dyadic and limit children of f3decb5b-3c0d-4063-b885-79044b1ecb2f.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDyadicPairsAEMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (n : ℕ) :
    AEMeasurable (fun ω : Omega =>
      let a := sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))
      (a, a - X t ω)) P ∧
    AEMeasurable (fun ω : Omega =>
      let b := sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))
      (X t ω - b, -b)) P := by sorry
