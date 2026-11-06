-- Prove2me | Theorems.Thm_OAI_IdealGaussCRT_crt_right_inverse_coordinate
-- name    : OAI.IdealGaussCRT.crt_right_inverse_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:57.301938+00:00
-- url     : https://prove2.me/theorems/f337163f-9de6-44e8-9f45-efd655e91957
-- title:
--   Ideal Gauss CRT: crt right inverse coordinate
-- statement:
--   The Ideal Gauss CRT construction uses the crt right inverse coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L404-L436
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L404-L436

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

theorem OAI.IdealGaussCRT.crt_right_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (y : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by sorry
