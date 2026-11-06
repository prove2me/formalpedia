-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_rows_within_norm_cutoff
-- name    : OAI.ActualEisensteinCubic.sixth_power_rows_within_norm_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:11.137726+00:00
-- url     : https://prove2.me/theorems/53ee7ea2-6925-44b2-9448-d0ca8f6ddb8d
-- title:
--   Actual Eisenstein Cubic: sixth power rows within norm cutoff
-- statement:
--   The Actual Eisenstein Cubic construction uses the sixth power rows within norm cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L26-L52
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L26-L52

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

theorem OAI.ActualEisensteinCubic.sixth_power_rows_within_norm_cutoff
    {β : Type*} (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hcover : ∀ u : O,
      (Ideal.absNorm (Ideal.span {u}) : ℝ) ≤
        (D : ℝ) ^ (11 / 10 : ℝ) → u ∈ rows) :
    selected.image (fun i => p i ^ 6) ⊆ rows := by sorry
