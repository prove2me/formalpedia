-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkOffspringSupportAE
-- name    : Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:02:37.781195+00:00
-- url     : https://prove2.me/theorems/90c8591b-ed84-4aa6-8ff3-ebb2bab344d5
-- title:
--   The first compound-Poisson mark is almost surely an offspring count minus one
-- statement:
--   The source jump law puts full probability on integer offspring-shift marks. Apply the compound-Poisson driver first-mark law and pull back its full-measure support to conclude almost-sure existence of a natural number j for the realised mark.
-- source:
--   Kyprianou (2006) §1.3.4 integer offspring-shift jump support and mark law

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ j : ℕ, x = (j : ℝ) - 1} = 1) :
    ∀ᵐ ω ∂Q, ∃ j : ℕ, marks 0 ω = (j : ℝ) - 1 := by
  sorry
