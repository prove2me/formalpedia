-- Prove2me | Theorems.Thm_OAI_IdealGaussCRT_gauss_sum_crt
-- name    : OAI.IdealGaussCRT.gauss_sum_crt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:50.327024+00:00
-- url     : https://prove2.me/theorems/1a062151-a5f5-493a-843b-1370a144f94a
-- title:
--   Ideal Gauss CRT: gauss sum crt
-- statement:
--   The Ideal Gauss CRT construction uses the gauss sum crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L287-L309
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L287-L309

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
open scoped Classical
open OAI.IdealGaussCRT
variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

theorem OAI.IdealGaussCRT.gauss_sum_crt [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ x) =
      gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by sorry
