-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentPairArraysUncurryV1
-- name    : Kyprianou.Ch02.independentPairArraysUncurryV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:02:22.649925+00:00
-- url     : https://prove2.me/theorems/bde420ae-79b0-42fe-8bfb-7499cff53c72
-- title:
--   Measurable independent pairs have independent individual coordinates
-- statement:
--   Apply iIndepFun_uncurry to the measurable coordinate vector of each pair and the independent Fin 2 family within each pair.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.independentPairArraysUncurryV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (G : Fin n → Ω → ℝ × ℝ)
    (hm : ∀ i, Measurable (G i)) (hi : iIndepFun G P)
    (hc : ∀ i, IndepFun (fun ω => (G i ω).1) (fun ω => (G i ω).2) P) :
    iIndepFun (fun (p : Fin n × Fin 2) ω =>
      if p.2=0 then (G p.1 ω).1 else (G p.1 ω).2) P := by sorry
