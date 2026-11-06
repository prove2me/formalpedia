-- Prove2me | Theorems.Thm_OAI_GaussCRT_addChar_crt_factor
-- name    : OAI.GaussCRT.addChar_crt_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:06.599356+00:00
-- url     : https://prove2.me/theorems/779d8076-29a8-4b20-becf-fb584e90fff8
-- title:
--   Gauss CRT: add Char crt factor
-- statement:
--   The Gauss CRT construction uses the add Char crt factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L76-L89
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L76-L89

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

theorem OAI.GaussCRT.addChar_crt_factor (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) (x : ZMod (m * n)) :
    ψ x =
      leftAddChar m n h ψ ((ZMod.chineseRemainder h x).1) *
      rightAddChar m n h ψ ((ZMod.chineseRemainder h x).2) := by sorry
