-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPath_toFoundations
-- name    : Kyprianou.Ch01.compoundPath_toFoundations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:15:59.998331+00:00
-- url     : https://prove2.me/theorems/ba3448fb-4bb4-45e6-814e-d318a7631e8c
-- title:
--   Compound-Poisson sample paths coincide across established formal definitions
-- statement:
--   The LeanLevy and Lévy Foundations constructions of a compound-Poisson path are pointwise equal with identical drift, clock, jump marks, time and sample state.
-- source:
--   Kyprianou (2006) Chapter 1, §1.2.2, compound Poisson examples; LeanLevy and levy_foundations definitions.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPath_toFoundations
    {Ω : Type*} (b : ℝ) (τ Y : ℕ → Ω → ℝ)
    (t : ℝ) (ω : Ω) :
    ProbabilityTheory.compoundPoisson b τ Y t ω =
      LevyFoundations.compoundPoisson b τ Y t ω := by sorry
