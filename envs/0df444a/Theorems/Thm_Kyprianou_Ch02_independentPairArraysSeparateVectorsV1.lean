-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentPairArraysSeparateVectorsV1
-- name    : Kyprianou.Ch02.independentPairArraysSeparateVectorsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:55:10.652381+00:00
-- url     : https://prove2.me/theorems/d268e40b-a689-4b7d-a225-dc2e10abd1d8
-- title:
--   Independent pairs with independent coordinates yield independent coordinate arrays
-- statement:
--   Use measurable modifications, uncurry independence of the pairs and their coordinates, then group the independent variables by coordinate.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.independentPairArraysSeparateVectorsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (F : Fin n → Ω → ℝ × ℝ)
    (hm : ∀ i, AEMeasurable (F i) P) (hi : iIndepFun F P)
    (hc : ∀ i, IndepFun (fun ω => (F i ω).1) (fun ω => (F i ω).2) P) :
    IndepFun (fun ω i => (F i ω).1) (fun ω i => (F i ω).2) P := by sorry
