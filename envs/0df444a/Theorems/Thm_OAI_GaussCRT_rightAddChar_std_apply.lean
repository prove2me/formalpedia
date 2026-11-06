-- Prove2me | Theorems.Thm_OAI_GaussCRT_rightAddChar_std_apply
-- name    : OAI.GaussCRT.rightAddChar_std_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:45.49031+00:00
-- url     : https://prove2.me/theorems/f2931b9e-c3ca-40e2-b6b9-c32237886d82
-- title:
--   Gauss CRT: right Add Char std apply
-- statement:
--   The Gauss CRT construction uses the right Add Char std apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L172-L195
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L172-L195

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

theorem OAI.GaussCRT.rightAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := n)) ((r : ZMod n) * z) := by sorry
