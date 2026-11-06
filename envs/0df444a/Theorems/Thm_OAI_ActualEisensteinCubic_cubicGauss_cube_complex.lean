-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_cube_complex
-- name    : OAI.ActualEisensteinCubic.cubicGauss_cube_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:20:09.350385+00:00
-- url     : https://prove2.me/theorems/bf12896d-be19-4a9e-aff3-2eacb6a93e10
-- title:
--   Actual Eisenstein Cubic: cubic Gauss cube complex
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Gauss cube complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1214-L1223
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1214-L1223

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
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
open OAI.ActualEisensteinCubic

theorem OAI.ActualEisensteinCubic.cubicGauss_cube_complex (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) ^ 3 =
      -(ringComplex p) * (Nat.card (O ⧸ P) : ℂ) := by sorry
