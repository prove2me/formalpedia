-- Prove2me | Theorems.Thm_Kyprianou_Ch02_threeIndependentOfPairIndepV1
-- name    : Kyprianou.Ch02.threeIndependentOfPairIndepV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:42:29.222182+00:00
-- url     : https://prove2.me/theorems/2c5a08de-243e-4560-9a65-e89caabb93bd
-- title:
--   Three functions mutually independent from two nested pair independence conditions
-- statement:
--   If G is independent of the pair (L,S) and L and S are independent, the three functions are mutually independent.
-- source:
--   Kyprianou (2006), Chapter 2, mutual independence via full rectangle factorisation

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch02.threeIndependentOfPairIndepV1
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G L S : Ω → E)
    (hGP : IndepFun G (fun ω => (L ω, S ω)) P)
    (hLS : IndepFun L S P) :
    iIndepFun (fun (i : Fin 3) (ω : Ω) =>
      if i = 0 then G ω else if i = 1 then L ω else S ω) P := by sorry
