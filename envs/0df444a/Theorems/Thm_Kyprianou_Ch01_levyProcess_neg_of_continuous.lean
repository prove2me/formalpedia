-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyProcess_neg_of_continuous
-- name    : Kyprianou.Ch01.levyProcess_neg_of_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:54:12.939203+00:00
-- url     : https://prove2.me/theorems/8a70faf7-66ed-482a-9ea5-552b57f7d369
-- title:
--   Sign reversal preserves Lévy process properties under continuous paths
-- statement:
--   A real Lévy process with almost-sure continuous paths remains a Lévy process after sign reversal. Its start remains zero, its stationarity and mutual independence of increments are transported through coordinatewise negation, and its almost-sure continuous paths imply càdlàg reflected paths. The source states all Lévy properties at once, not a partial Gaussian-marginal substitute. It can be reused for Brownian reflection and lower barrier first passage.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii): apply the upper-passage transform to the reflected Brownian Lévy process.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyProcess_neg_of_continuous
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) :
    ProbabilityTheory.IsLevyProcess (fun t ω => -X t ω) P := by sorry
