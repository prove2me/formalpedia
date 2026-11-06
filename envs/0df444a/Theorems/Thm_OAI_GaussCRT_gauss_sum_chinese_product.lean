-- Prove2me | Theorems.Thm_OAI_GaussCRT_gauss_sum_chinese_product
-- name    : OAI.GaussCRT.gauss_sum_chinese_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:47.935539+00:00
-- url     : https://prove2.me/theorems/6db97b6b-d159-4ae9-94f3-e51b877c51ab
-- title:
--   Gauss CRT: gauss sum chinese product
-- statement:
--   The Gauss CRT construction uses the gauss sum chinese product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L19-L48
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L19-L48

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex
open scoped Classical
open OAI.GaussCRT

theorem OAI.GaussCRT.gauss_sum_chinese_product (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψm : AddChar (ZMod m) ℂ) (ψn : AddChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
      gaussSum χm ψm * gaussSum χn ψn := by sorry
