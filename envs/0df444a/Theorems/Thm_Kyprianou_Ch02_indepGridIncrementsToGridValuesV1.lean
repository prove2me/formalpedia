-- Prove2me | Theorems.Thm_Kyprianou_Ch02_indepGridIncrementsToGridValuesV1
-- name    : Kyprianou.Ch02.indepGridIncrementsToGridValuesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:22:13.926477+00:00
-- url     : https://prove2.me/theorems/0a274c46-a1fc-4ef7-b63e-d55f20258f24
-- title:
--   Independent coordinate increment vectors give independent grid value vectors
-- statement:
--   Independent coordinate increment vectors give independent grid value vectors
-- source:
--   Kyprianou (2006), Exercise 2.8, finite-grid independence argument.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.indepGridIncrementsToGridValuesV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : ℝ≥0 → Ω → ℝ) (hA0 : A 0 = fun _ => 0)
    (hB0 : B 0 = fun _ => 0) (n : ℕ)
    (t : Fin (n+1) → ℝ≥0) (ht0 : t 0 = 0)
    (hi : IndepFun (fun ω (i : Fin n) => A (t i.succ) ω - A (t i.castSucc) ω)
      (fun ω (i : Fin n) => B (t i.succ) ω - B (t i.castSucc) ω) P) :
    IndepFun (fun ω k => A (t k) ω) (fun ω k => B (t k) ω) P := by sorry
