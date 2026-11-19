-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarksIdentDistrib
-- name    : Kyprianou.Ch01.compoundPoissonMarksIdentDistrib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:50:19.897737+00:00
-- url     : https://prove2.me/theorems/35804c44-f2ef-43b1-a27b-3439852c2047
-- title:
--   Identical distribution of all Lévy compound-Poisson marks
-- statement:
--   For a source-faithful LeanLevy compound Poisson driver, every mark has the exact same law as the first mark. This converts the driver's HasLaw data into the IdentDistrib hypothesis required by the full IID strong law.
-- source:
--   LeanLevy Processes CompoundPoisson, driver law_mark field; Chapter 1 source finite-mean strong-law proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonMarksIdentDistrib
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival marks : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw P) :
    ∀ n : ℕ, IdentDistrib (marks n) (marks 0) P P := by
  sorry
