-- Prove2me | Theorems.Thm_OAI_JacobiQuadratic_jacobi_quadratic
-- name    : OAI.JacobiQuadratic.jacobi_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:32.895269+00:00
-- url     : https://prove2.me/theorems/844a51f2-1a55-41af-ba9a-ac8cb94707e0
-- title:
--   Jacobi Quadratic: jacobi quadratic
-- statement:
--   The Jacobi Quadratic construction uses the jacobi quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L509-L543
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L509-L543

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
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
open OAI.JacobiQuadratic
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem OAI.JacobiQuadratic.jacobi_quadratic (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) (hχ : χ ≠ 1) :
    jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) =
      χ (4 : F) * jacobiSum χ χ := by sorry
