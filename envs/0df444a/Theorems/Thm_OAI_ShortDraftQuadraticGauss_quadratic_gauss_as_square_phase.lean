-- Prove2me | Theorems.Thm_OAI_ShortDraftQuadraticGauss_quadratic_gauss_as_square_phase
-- name    : OAI.ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:30.514267+00:00
-- url     : https://prove2.me/theorems/10ce4ab4-772a-4702-a961-7c9aaa04a1ef
-- title:
--   Short Draft Quadratic Gauss: quadratic gauss as square phase
-- statement:
--   The Short Draft Quadratic Gauss construction uses the quadratic gauss as square phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L289-L315
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L289-L315

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
open OAI.ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem OAI.ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by sorry
