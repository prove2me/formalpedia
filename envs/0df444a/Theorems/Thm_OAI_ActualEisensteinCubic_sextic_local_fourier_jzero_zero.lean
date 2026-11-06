-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sextic_local_fourier_jzero_zero
-- name    : OAI.ActualEisensteinCubic.sextic_local_fourier_jzero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:37:41.603921+00:00
-- url     : https://prove2.me/theorems/e51fa16f-3224-40ae-80ed-36dde89a310b
-- title:
--   Actual Eisenstein Cubic: sextic local fourier jzero zero
-- statement:
--   The Actual Eisenstein Cubic construction uses the sextic local fourier jzero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L445-L457
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L445-L457

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

theorem OAI.ActualEisensteinCubic.sextic_local_fourier_jzero_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ 0) y *
        ψ (-(0 : O ⧸ P) * y)) = (Nat.card (O ⧸ P) : ℂ) - 1 := by sorry
