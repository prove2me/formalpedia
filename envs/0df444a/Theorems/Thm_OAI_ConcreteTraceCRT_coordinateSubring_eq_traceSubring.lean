-- Prove2me | Theorems.Thm_OAI_ConcreteTraceCRT_coordinateSubring_eq_traceSubring
-- name    : OAI.ConcreteTraceCRT.coordinateSubring_eq_traceSubring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:36:48.207126+00:00
-- url     : https://prove2.me/theorems/689ecccf-da8a-4f2c-8d60-a72c40a5869b
-- title:
--   Concrete Trace CRT: coordinate Subring eq trace Subring
-- statement:
--   The Concrete Trace CRT construction uses the coordinate Subring eq trace Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L192-L194
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L192-L194

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

theorem OAI.ConcreteTraceCRT.coordinateSubring_eq_traceSubring :
    coordinateSubring = ShortDraftTrace.eisensteinSubring := by sorry
