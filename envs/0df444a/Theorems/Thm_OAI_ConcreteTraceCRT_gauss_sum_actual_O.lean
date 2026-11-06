-- Prove2me | Theorems.Thm_OAI_ConcreteTraceCRT_gauss_sum_actual_O
-- name    : OAI.ConcreteTraceCRT.gauss_sum_actual_O
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:36:23.807073+00:00
-- url     : https://prove2.me/theorems/3b83a546-b5bc-4882-8490-f85d99abc0c7
-- title:
--   Concrete Trace CRT: gauss sum actual O
-- statement:
--   The Concrete Trace CRT construction uses the gauss sum actual O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L241-L265
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L241-L265

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
open OAI.ConcreteTraceCRT
open EisensteinEmbedding IdealGaussCRT

theorem OAI.ConcreteTraceCRT.gauss_sum_actual_O
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ c d : ℤ,
      ψ (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ψ hperiod a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ψ hperiod a ha) *
      gaussSum χb (eisTraceModChar ψ hperiod b hb) := by sorry
