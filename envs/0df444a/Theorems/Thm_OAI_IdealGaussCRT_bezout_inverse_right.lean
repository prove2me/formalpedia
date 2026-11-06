-- Prove2me | Theorems.Thm_OAI_IdealGaussCRT_bezout_inverse_right
-- name    : OAI.IdealGaussCRT.bezout_inverse_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:52:10.281197+00:00
-- url     : https://prove2.me/theorems/8ebb87e1-4daa-42d5-955f-6cfa46994267
-- title:
--   Ideal Gauss CRT: bezout inverse right
-- statement:
--   The Ideal Gauss CRT construction uses the bezout inverse right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L567-L578
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L567-L578

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

theorem OAI.IdealGaussCRT.bezout_inverse_right {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {b}) a) *
      (Ideal.Quotient.mk (Ideal.span {b}) u) = 1 := by sorry
