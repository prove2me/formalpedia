-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
-- name    : OAI.ActualEisensteinCubic.canonicalSextic_pow_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:36:11.682806+00:00
-- url     : https://prove2.me/theorems/cd674efb-211f-451d-98d8-9980cc103b00
-- title:
--   Actual Eisenstein Cubic: canonical Sextic pow ne one
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical Sextic pow ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L471-L480
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L471-L480

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
open AddChar MulChar

theorem OAI.ActualEisensteinCubic.canonicalSextic_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    canonicalSextic P hgood ^ j ≠ 1 := by sorry
