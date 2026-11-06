-- Prove2me | Theorems.Thm_OAI_GaussCRT_gauss_sum_crt_standard
-- name    : OAI.GaussCRT.gauss_sum_crt_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:50.433573+00:00
-- url     : https://prove2.me/theorems/c1f55bac-706c-4ed6-aedd-8a95598b186c
-- title:
--   Gauss CRT: gauss sum crt standard
-- statement:
--   The Gauss CRT construction uses the gauss sum crt standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L223-L248
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L223-L248

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

theorem OAI.GaussCRT.gauss_sum_crt_standard (m n r s : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : m.Coprime n)
    (hr : ((n * r : ℕ) : ZMod m) = 1)
    (hs : ((m * s : ℕ) : ZMod n) = 1)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      (ZMod.stdAddChar (N := m * n)) x) =
      χm (n : ZMod m) * χn (m : ZMod n) *
        gaussSum χm (ZMod.stdAddChar (N := m)) *
        gaussSum χn (ZMod.stdAddChar (N := n)) := by sorry
