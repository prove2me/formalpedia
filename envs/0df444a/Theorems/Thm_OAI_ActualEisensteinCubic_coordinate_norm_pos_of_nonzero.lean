-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero
-- name    : OAI.ActualEisensteinCubic.coordinate_norm_pos_of_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:42.216194+00:00
-- url     : https://prove2.me/theorems/81d7a013-a0db-4071-8331-1425c180861e
-- title:
--   Actual Eisenstein Cubic: coordinate norm pos of nonzero
-- statement:
--   The Actual Eisenstein Cubic construction uses the coordinate norm pos of nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L480-L490
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L480-L490

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
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
open EisensteinEmbedding ConcreteTraceCRT Complex

theorem OAI.ActualEisensteinCubic.coordinate_norm_pos_of_nonzero (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    0 < a*a-a*b+b*b := by sorry
