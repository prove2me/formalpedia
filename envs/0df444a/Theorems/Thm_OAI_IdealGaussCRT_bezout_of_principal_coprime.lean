-- Prove2me | Theorems.Thm_OAI_IdealGaussCRT_bezout_of_principal_coprime
-- name    : OAI.IdealGaussCRT.bezout_of_principal_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:53.702352+00:00
-- url     : https://prove2.me/theorems/fb6cf392-2122-41db-a152-17bb41101ae8
-- title:
--   Ideal Gauss CRT: bezout of principal coprime
-- statement:
--   The Ideal Gauss CRT construction uses the bezout of principal coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L360-L368
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L360-L368

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

theorem OAI.IdealGaussCRT.bezout_of_principal_coprime {A : Type*} [CommRing A]
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by sorry
