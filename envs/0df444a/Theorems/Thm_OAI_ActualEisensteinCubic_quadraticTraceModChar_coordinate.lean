-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_quadraticTraceModChar_coordinate
-- name    : OAI.ActualEisensteinCubic.quadraticTraceModChar_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:57.376101+00:00
-- url     : https://prove2.me/theorems/9e1f816c-612c-4fc6-85df-d6dbfef037f4
-- title:
--   Actual Eisenstein Cubic: quadratic Trace Mod Char coordinate
-- statement:
--   The Actual Eisenstein Cubic construction uses the quadratic Trace Mod Char coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L339-L359
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L339-L359

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
open EisensteinEmbedding ConcreteTraceCRT Complex

theorem OAI.ActualEisensteinCubic.quadraticTraceModChar_coordinate (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval x y
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc)
      (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by sorry
