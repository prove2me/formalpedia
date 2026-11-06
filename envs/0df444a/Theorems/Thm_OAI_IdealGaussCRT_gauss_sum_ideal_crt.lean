-- Prove2me | Theorems.Thm_OAI_IdealGaussCRT_gauss_sum_ideal_crt
-- name    : OAI.IdealGaussCRT.gauss_sum_ideal_crt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:52:03.035886+00:00
-- url     : https://prove2.me/theorems/fe08f3e6-8f5b-4ccc-820d-884fc839dfff
-- title:
--   Ideal Gauss CRT: gauss sum ideal crt
-- statement:
--   The Ideal Gauss CRT construction uses the gauss sum ideal crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L311-L326
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L311-L326

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

theorem OAI.IdealGaussCRT.gauss_sum_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (h : IsCoprime I J)
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by sorry
