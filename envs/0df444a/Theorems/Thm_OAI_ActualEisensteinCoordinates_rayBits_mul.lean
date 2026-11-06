-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCoordinates_rayBits_mul
-- name    : OAI.ActualEisensteinCoordinates.rayBits_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:21:44.536206+00:00
-- url     : https://prove2.me/theorems/b3ea5d43-8ddf-4af5-bf82-3f16f6efe82f
-- title:
--   Actual Eisenstein Coordinates: ray Bits mul
-- statement:
--   The Actual Eisenstein Coordinates construction uses the ray Bits mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L658-L665
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L658-L665

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
open OAI.ActualEisensteinCoordinates

theorem OAI.ActualEisensteinCoordinates.rayBits_mul (x y : O)
    (hx : ¬ (2 : O) ∣ x) (hy : ¬ (2 : O) ∣ y) :
    rayBits (x*y) = rayBits x + rayBits y := by sorry
