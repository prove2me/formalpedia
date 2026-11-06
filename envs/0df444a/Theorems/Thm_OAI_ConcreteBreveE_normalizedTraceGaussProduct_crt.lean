-- Prove2me | Theorems.Thm_OAI_ConcreteBreveE_normalizedTraceGaussProduct_crt
-- name    : OAI.ConcreteBreveE.normalizedTraceGaussProduct_crt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:26.887982+00:00
-- url     : https://prove2.me/theorems/50712d6a-1a7e-41fd-876b-a3dac96802cc
-- title:
--   Concrete Breve E: normalized Trace Gauss Product crt
-- statement:
--   The Concrete Breve E construction uses the normalized Trace Gauss Product crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L277-L307
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L277-L307

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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
open OAI.ConcreteBreveE
open EisensteinEmbedding ConcreteTraceCRT

theorem OAI.ConcreteBreveE.normalizedTraceGaussProduct_crt
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    normalizedTraceGaussProduct a b ha hb χa χb =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      normalizedTraceGauss a ha χa * normalizedTraceGauss b hb χb := by sorry
