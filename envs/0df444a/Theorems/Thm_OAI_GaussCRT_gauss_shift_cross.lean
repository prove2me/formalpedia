-- Prove2me | Theorems.Thm_OAI_GaussCRT_gauss_shift_cross
-- name    : OAI.GaussCRT.gauss_shift_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:51.792145+00:00
-- url     : https://prove2.me/theorems/6cef0132-3835-4b2a-b453-285d07e5d232
-- title:
--   Gauss CRT: gauss shift cross
-- statement:
--   The Gauss CRT construction uses the gauss shift cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L197-L221
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L197-L221

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

theorem OAI.GaussCRT.gauss_shift_cross (m n r : ℕ) [NeZero m]
    (χ : MulChar (ZMod m) ℂ)
    (hr : ((n * r : ℕ) : ZMod m) = 1) :
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by sorry
