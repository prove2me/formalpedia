-- Prove2me | Theorems.Thm_OAI_ShortDraftGauss_norm_gaussSum_eq_sqrt_card
-- name    : OAI.ShortDraftGauss.norm_gaussSum_eq_sqrt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:21:39.476004+00:00
-- url     : https://prove2.me/theorems/a74c0f97-45d3-4f26-9f07-2b9dbc64c968
-- title:
--   Short Draft Gauss: norm gauss Sum eq sqrt card
-- statement:
--   The Short Draft Gauss construction uses the norm gauss Sum eq sqrt card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L120-L137
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L120-L137

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ShortDraftGauss
open Complex
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]

theorem OAI.ShortDraftGauss.norm_gaussSum_eq_sqrt_card (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by sorry
