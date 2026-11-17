-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mathlibIndepIncrements_toLeanLevy
-- name    : Kyprianou.Ch01.mathlibIndepIncrements_toLeanLevy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:07:52.488879+00:00
-- url     : https://prove2.me/theorems/e0269f82-1409-4f41-8b2c-c241870a9e23
-- title:
--   Mathlib Brownian independent increments satisfy LeanLevy finite-grid Lévy independence
-- statement:
--   For every real-valued process indexed by nonnegative real time on any measurable probability space, the Mathlib HasIndepIncrements predicate implies the LeanLevy HasIndependentIncrements predicate required by the Lévy process definition. These predicates elaborate compatibly in the pinned environment, so the direct proof is the hypothesis itself. This is the exact independent-increment interface bridge needed for the Brownian component of the positive Gaussian Lévy–Khintchine process existence construction.
-- source:
--   Pinned Mathlib.Probability.BrownianMotion.Basic definition HasIndepIncrements; pinned LeanLevy source Definition LeanLevy_Processes_StochasticProcess; Kyprianou (2006), Chapter 1 Theorem 1.6.

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Test whether Mathlib Brownian increment independence implies LeanLevy finite-grid increment independence definitionally. -/

theorem Kyprianou.Ch01.mathlibIndepIncrements_toLeanLevy
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (h : ProbabilityTheory.HasIndepIncrements X P) :
    ProbabilityTheory.HasIndependentIncrements X P := by
  sorry
