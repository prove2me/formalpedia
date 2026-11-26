-- Prove2me | Theorems.Thm_MeasureTheory_Martingale_square_sub_pathwiseQuadraticVariation
-- name    : MeasureTheory.Martingale.square_sub_pathwiseQuadraticVariation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:47.230547+00:00
-- url     : https://prove2.me/theorems/71d7ee6c-aff6-58bc-bc5e-57940255058e
-- title:
--   Square minus discrete pathwise quadratic variation is a martingale
-- statement:
--   For a square-integrable discrete-time real martingale, its square minus its pathwise quadratic variation is a martingale.
-- source:
--   StochLean.Probability.Martingale.QuadraticVariation

import Definitions.Def_SourceProof_549506abde5375992c159de2

open MeasureTheory
open scoped BigOperators ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem MeasureTheory.Martingale.square_sub_pathwiseQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) :
    Martingale (squareMinusPathwiseQuadraticVariation M) 𝓕 μ := by sorry
