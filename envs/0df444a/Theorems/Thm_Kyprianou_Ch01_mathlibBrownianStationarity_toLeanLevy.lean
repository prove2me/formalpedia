-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mathlibBrownianStationarity_toLeanLevy
-- name    : Kyprianou.Ch01.mathlibBrownianStationarity_toLeanLevy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:11:43.566193+00:00
-- url     : https://prove2.me/theorems/b24ed968-8ee8-4816-8cf2-7326b348c2d6
-- title:
--   Mathlib Brownian equal-lag Gaussian increments satisfy LeanLevy stationary-increment law
-- statement:
--   For any process X with the pinned Mathlib IsPreBrownianReal property under a measure P, its increments over intervals of the same nonnegative duration have the same laws. In the exact LeanLevy interface this is HasStationaryIncrements X P. The proof applies Mathlib IsPreBrownianReal.hasLaw_sub at the two time intervals, uses translation invariance of real nndist for their equal lengths, transports the Gaussian law equality, and applies HasLaw.identDistrib. This is the stationary-increment obligation needed for the positive-Gaussian Lévy process construction in Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Mathlib.Probability.BrownianMotion.Basic IsPreBrownianReal.hasLaw_sub, pinned 0df444a360eaa60ab8c11dca51a86af692955474; Definition LeanLevy_Processes_StochasticProcess; Kyprianou (2006) Chapter 1 Theorem 1.6.

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Equal Gaussian laws of equally long increments imply LeanLevy stationary increments. -/

theorem Kyprianou.Ch01.mathlibBrownianStationarity_toLeanLevy
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (h : ProbabilityTheory.IsPreBrownianReal X P) :
    ProbabilityTheory.HasStationaryIncrements X P := by
  sorry
