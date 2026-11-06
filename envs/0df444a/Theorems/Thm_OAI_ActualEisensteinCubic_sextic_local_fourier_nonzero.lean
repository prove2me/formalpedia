-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sextic_local_fourier_nonzero
-- name    : OAI.ActualEisensteinCubic.sextic_local_fourier_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:37:40.53221+00:00
-- url     : https://prove2.me/theorems/84a2a97e-912d-4953-a55b-4a518fbc0c38
-- title:
--   Actual Eisenstein Cubic: sextic local fourier nonzero
-- statement:
--   The Actual Eisenstein Cubic construction uses the sextic local fourier nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L401-L417
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L401-L417

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
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
open AddChar MulChar

theorem OAI.ActualEisensteinCubic.sextic_local_fourier_nonzero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6)
    (h : O ⧸ P) (hh : h ≠ 0) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ j) y * ψ (-h * y)) =
    ((((sexticChar P hgood).ringHomComp ringComplex) ^ j) h)⁻¹ *
      gaussSum (((sexticChar P hgood).ringHomComp ringComplex) ^ j)
        (ψ.mulShift (-1)) := by sorry
