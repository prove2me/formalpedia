-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_mellin_of_exponential_smoothing
-- name    : OAI.ShortDraftMellin.mellin_of_exponential_smoothing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:20.222756+00:00
-- url     : https://prove2.me/theorems/13a7f3d4-ae37-4bea-952b-7ba2bb4cc936
-- title:
--   Short Draft Mellin: mellin of exponential smoothing
-- statement:
--   The Short Draft Mellin construction uses the mellin of exponential smoothing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L445-L482
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L445-L482

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin

theorem OAI.ShortDraftMellin.mellin_of_exponential_smoothing
    (a : ℕ → ℂ) (F : ℝ → ℂ) (s : ℂ)
    (hs : 1 < s.re) (ha0 : a 0 = 0)
    (hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t)) (F t))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) = Complex.Gamma s * LSeries a s := by sorry
