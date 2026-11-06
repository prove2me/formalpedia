-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_breveLocalG_eq_conjugate
-- name    : OAI.ActualEisensteinCubic.breveLocalG_eq_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:13:35.601114+00:00
-- url     : https://prove2.me/theorems/38f013ea-6ce7-454a-81e8-bb6003319f5b
-- title:
--   Actual Eisenstein Cubic: breve Local G eq conjugate
-- statement:
--   The Actual Eisenstein Cubic construction uses the breve Local G eq conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L34-L47
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L34-L47

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
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
open ConcreteTraceCRT
open scoped ComplexConjugate

theorem OAI.ActualEisensteinCubic.breveLocalG_eq_conjugate (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    breveLocalG P hgood p hP hp =
      star (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O))) *
        breveGamma3 P hgood p hP hp := by sorry
