-- Prove2me | Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_product
-- name    : OAI.ConcreteTraceCRT.finite_quotient_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:37:16.094773+00:00
-- url     : https://prove2.me/theorems/f99812c0-8133-4372-a742-2ae79d98ab27
-- title:
--   Concrete Trace CRT: finite quotient product
-- statement:
--   The Concrete Trace CRT construction uses the finite quotient product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L273-L279
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L273-L279

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

theorem OAI.ConcreteTraceCRT.finite_quotient_product {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := by sorry
