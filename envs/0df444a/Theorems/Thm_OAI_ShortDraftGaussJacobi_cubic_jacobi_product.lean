-- Prove2me | Theorems.Thm_OAI_ShortDraftGaussJacobi_cubic_jacobi_product
-- name    : OAI.ShortDraftGaussJacobi.cubic_jacobi_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:27.484858+00:00
-- url     : https://prove2.me/theorems/636c68aa-8cf1-4c27-ac9e-b97f86024393
-- title:
--   Short Draft Gauss Jacobi: cubic jacobi product
-- statement:
--   The Short Draft Gauss Jacobi construction uses the cubic jacobi product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L225-L239
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L225-L239

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
open OAI.ShortDraftGaussJacobi
open Finset
variable {F : Type*} [Field F] [Fintype F]

theorem OAI.ShortDraftGaussJacobi.cubic_jacobi_product (χ : MulChar F ℂ)
    (horder : orderOf χ = 3)
    (hchar : ringChar ℂ ≠ ringChar F) :
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = (Fintype.card F : ℂ) := by sorry
