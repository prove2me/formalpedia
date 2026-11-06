-- Prove2me | Theorems.Thm_OAI_GaussCRT_gauss_sum_crt
-- name    : OAI.GaussCRT.gauss_sum_crt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:59.137055+00:00
-- url     : https://prove2.me/theorems/9caa5845-fb2e-4ed1-9ced-85b80264b427
-- title:
--   Gauss CRT: gauss sum crt
-- statement:
--   The Gauss CRT construction uses the gauss sum crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L91-L103
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L91-L103

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

theorem OAI.GaussCRT.gauss_sum_crt (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψ : AddChar (ZMod (m * n)) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) * ψ x) =
      gaussSum χm (leftAddChar m n h ψ) *
      gaussSum χn (rightAddChar m n h ψ) := by sorry
