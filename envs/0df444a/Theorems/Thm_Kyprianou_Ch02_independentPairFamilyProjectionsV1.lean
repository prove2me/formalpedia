-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentPairFamilyProjectionsV1
-- name    : Kyprianou.Ch02.independentPairFamilyProjectionsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:21:55.425069+00:00
-- url     : https://prove2.me/theorems/162b024c-149b-4dee-8481-1a944945917b
-- title:
--   Independent pairs with independent coordinates yield independent projected arrays
-- statement:
--   Use the bounded continuous product-test characterisation of array independence. Independence of the pairs splits the joint product into one expectation per pair, coordinate independence splits each of those, and independence of the projections identifies the separate products.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.independentPairFamilyProjectionsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (a b : Fin n → Ω → ℝ)
    (ha : ∀ i, AEMeasurable (a i) P) (hb : ∀ i, AEMeasurable (b i) P)
    (hi : iIndepFun (fun i ω => (a i ω,b i ω)) P)
    (hc : ∀ i, IndepFun (a i) (b i) P) :
    IndepFun (fun ω i => a i ω) (fun ω i => b i ω) P := by sorry
