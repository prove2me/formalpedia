-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_six
-- name    : OAI.ActualEisensteinCubic.canonicalSextic_pow_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:36:27.795205+00:00
-- url     : https://prove2.me/theorems/c6b71ff9-8fb2-4df2-bbfa-d7d1c5536e88
-- title:
--   Actual Eisenstein Cubic: canonical Sextic pow six
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical Sextic pow six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L465-L469
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L465-L469

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

theorem OAI.ActualEisensteinCubic.canonicalSextic_pow_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : canonicalSextic P hgood ^ 6 = 1 := by sorry
