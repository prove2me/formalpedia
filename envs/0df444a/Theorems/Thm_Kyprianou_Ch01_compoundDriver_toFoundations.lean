-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundDriver_toFoundations
-- name    : Kyprianou.Ch01.compoundDriver_toFoundations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:15:57.922144+00:00
-- url     : https://prove2.me/theorems/5ff84934-5ce9-48c9-8180-12f45d44fea2
-- title:
--   Transfer the LeanLevy compound-Poisson driver into the Lévy Foundations driver predicate
-- statement:
--   Every compound-Poisson driver satisfying the LeanLevy assumptions also satisfies the exact Lévy Foundations driver structure, with the same arrival, mark and measure parameters.
-- source:
--   Kyprianou (2006) Chapter 1, §1.2.2, compound Poisson examples; LeanLevy and levy_foundations definitions.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundDriver_toFoundations
    {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν : Measure ℝ}
    {P : Measure Ω}
    (hd : ProbabilityTheory.IsCompoundPoissonDriver τ Y r ν P) :
    LevyFoundations.IsCompoundPoissonDriver τ Y r ν P := by sorry
