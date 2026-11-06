-- Prove2me | Theorems.Thm_OAI_ShortDraftGauss_norm_normalized_gaussSum
-- name    : OAI.ShortDraftGauss.norm_normalized_gaussSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:14.105491+00:00
-- url     : https://prove2.me/theorems/6af18de7-0437-46ec-8def-b0fb0b93a935
-- title:
--   Short Draft Gauss: norm normalized gauss Sum
-- statement:
--   The Short Draft Gauss construction uses the norm normalized gauss Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L139-L148
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L139-L148

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

theorem OAI.ShortDraftGauss.norm_normalized_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ)⁻¹ * gaussSum χ ψ‖ = 1 := by sorry
