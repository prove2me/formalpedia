-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonical_two_prime_gauss_transform
-- name    : OAI.ActualEisensteinCubic.canonical_two_prime_gauss_transform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:19:49.139374+00:00
-- url     : https://prove2.me/theorems/c3a509a6-072f-474d-b3fe-b8b545a9332b
-- title:
--   Actual Eisenstein Cubic: canonical two prime gauss transform
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical two prime gauss transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L531-L565
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L531-L565

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
open OAI.ActualEisensteinCubic
open AddChar MulChar

theorem OAI.ActualEisensteinCubic.canonical_two_prime_gauss_transform
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hc : IsCoprime P Q)
    [Fintype (O ⧸ P * Q)] [Fintype (O ⧸ P)] [Fintype (O ⧸ Q)]
    (hgoodP : lambda ∉ P) (hgoodQ : lambda ∉ Q)
    (hcharP : ringChar (O ⧸ P) ≠ 2)
    (hcharQ : ringChar (O ⧸ Q) ≠ 2)
    (j k : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6)
    (hk0 : k ≠ 0) (hk6 : k < 6)
    (ψ : AddChar (O ⧸ P * Q) ℂ) (h : O ⧸ P * Q) :
    (∑ x : O ⧸ P * Q,
      (canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) x) *
      (canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h = 0
        then 0 else
        ((canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h))⁻¹ *
          gaussSum (canonicalSextic P hgoodP ^ j)
            (IdealGaussCRT.leftAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h = 0
        then 0 else
        ((canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h))⁻¹ *
          gaussSum (canonicalSextic Q hgoodQ ^ k)
            (IdealGaussCRT.rightAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) := by sorry
