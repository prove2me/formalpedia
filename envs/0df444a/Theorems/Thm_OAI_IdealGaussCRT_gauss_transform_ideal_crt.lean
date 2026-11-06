-- Prove2me | Theorems.Thm_OAI_IdealGaussCRT_gauss_transform_ideal_crt
-- name    : OAI.IdealGaussCRT.gauss_transform_ideal_crt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:19:15.137191+00:00
-- url     : https://prove2.me/theorems/14ac4455-690c-40e5-9d55-de25e099a5f1
-- title:
--   Ideal Gauss CRT: gauss transform ideal crt
-- statement:
--   The Ideal Gauss CRT construction uses the gauss transform ideal crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L428-L455
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L428-L455

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.IdealGaussCRT
open AddChar MulChar

theorem OAI.IdealGaussCRT.gauss_transform_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (hc : IsCoprime I J)
    [I.IsMaximal] [J.IsMaximal]
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ)
    (hχI : χI ≠ 1) (hχJ : χJ ≠ 1)
    (h : A ⧸ I * J) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h = 0
        then 0 else
        (χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h))⁻¹ *
          gaussSum χI
            (leftAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h = 0
        then 0 else
        (χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h))⁻¹ *
          gaussSum χJ
            (rightAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) := by sorry
