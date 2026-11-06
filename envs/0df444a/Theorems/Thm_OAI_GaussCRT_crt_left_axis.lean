-- Prove2me | Theorems.Thm_OAI_GaussCRT_crt_left_axis
-- name    : OAI.GaussCRT.crt_left_axis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:41.531701+00:00
-- url     : https://prove2.me/theorems/c123549f-e15c-42d6-8027-964d8e5255a2
-- title:
--   Gauss CRT: crt left axis
-- statement:
--   The Gauss CRT construction uses the crt left axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L105-L124
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L105-L124

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

theorem OAI.GaussCRT.crt_left_axis (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    (ZMod.chineseRemainder h).symm (z, 0) =
      ((n * r * z.val : ℕ) : ZMod (m * n)) := by sorry
