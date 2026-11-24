-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentRectangularColumnsV1
-- name    : Kyprianou.Ch02.independentRectangularColumnsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:02:21.335784+00:00
-- url     : https://prove2.me/theorems/2415e71d-304d-419b-96a8-768f0c15b863
-- title:
--   Independent scalar array has independent column vectors
-- statement:
--   Group independent scalar variables by their disjoint column index sets and restrict each column to its coordinate vector.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.independentRectangularColumnsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (D : Fin n × Fin 2 → Ω → ℝ)
    (hm : ∀ p, Measurable (D p)) (hi : iIndepFun D P) :
    IndepFun (fun ω (i : Fin n) => D (i,0) ω)
      (fun ω (i : Fin n) => D (i,1) ω) P := by sorry
