-- Prove2me | Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_primitive
-- name    : OAI.PrimitiveTrace.eisTraceModChar_breveE_primitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:38:05.67578+00:00
-- url     : https://prove2.me/theorems/6005f026-f45a-43ab-a33f-ad62f70a9b36
-- title:
--   Primitive Trace: eis Trace Mod Char breve E primitive
-- statement:
--   The Primitive Trace construction uses the eis Trace Mod Char breve E primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L687-L695
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L687-L695

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
open OAI.PrimitiveTrace
open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT

theorem OAI.PrimitiveTrace.eisTraceModChar_breveE_primitive
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp).IsPrimitive := by sorry
