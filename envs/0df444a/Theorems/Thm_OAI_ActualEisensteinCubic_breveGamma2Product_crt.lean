-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_breveGamma2Product_crt
-- name    : OAI.ActualEisensteinCubic.breveGamma2Product_crt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:33.608627+00:00
-- url     : https://prove2.me/theorems/cb6187dc-9b07-4168-afb6-349cd0f304e1
-- title:
--   Actual Eisenstein Cubic: breve Gamma2 Product crt
-- statement:
--   The Actual Eisenstein Cubic construction uses the breve Gamma2 Product crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L208-L247
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L208-L247

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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

theorem OAI.ActualEisensteinCubic.breveGamma2Product_crt
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [haMax : (Ideal.span {a}).IsMaximal]
    [hbMax : (Ideal.span {b}).IsMaximal]
    (hgooda : lambda ∉ Ideal.span {a})
    (hgoodb : lambda ∉ Ideal.span {b})
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    breveGamma2Product a b ha hb hgooda hgoodb =
      (canonicalSextic (Ideal.span {a}) hgooda
        (Ideal.Quotient.mk (Ideal.span {a}) b)) ^ 2 *
      (canonicalSextic (Ideal.span {b}) hgoodb
        (Ideal.Quotient.mk (Ideal.span {b}) a)) ^ 2 *
      breveGamma2 (Ideal.span {a}) hgooda a rfl ha *
      breveGamma2 (Ideal.span {b}) hgoodb b rfl hb := by sorry
