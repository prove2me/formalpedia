-- Prove2me | Theorems.Thm_OAI_GaussCRT_leftAddChar_std_apply
-- name    : OAI.GaussCRT.leftAddChar_std_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:55.485248+00:00
-- url     : https://prove2.me/theorems/e4d44500-146a-4f3d-a481-43dcce6a627d
-- title:
--   Gauss CRT: left Add Char std apply
-- statement:
--   The Gauss CRT construction uses the left Add Char std apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L126-L149
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L126-L149

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

theorem OAI.GaussCRT.leftAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := m)) ((r : ZMod m) * z) := by sorry
