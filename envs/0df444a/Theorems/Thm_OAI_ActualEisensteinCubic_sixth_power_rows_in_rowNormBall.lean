-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_rows_in_rowNormBall
-- name    : OAI.ActualEisensteinCubic.sixth_power_rows_in_rowNormBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:45:17.61935+00:00
-- url     : https://prove2.me/theorems/6a8ac4b0-f9e2-4767-a7a0-553ac55b15d8
-- title:
--   Actual Eisenstein Cubic: sixth power rows in row Norm Ball
-- statement:
--   The Actual Eisenstein Cubic construction uses the sixth power rows in row Norm Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L201-L214
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L201-L214

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic

theorem OAI.ActualEisensteinCubic.sixth_power_rows_in_rowNormBall
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ)) :
    selected.image (fun i => p i ^ 6) ⊆
      ShortDraftLatticeCount.rowNormBall H := by sorry
