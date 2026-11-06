-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_rationalCoordEquiv_apply
-- name    : OAI.ActualEisensteinCubic.rationalCoordEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:22:31.197599+00:00
-- url     : https://prove2.me/theorems/821f951f-d77d-4fe6-a184-0733c7954019
-- title:
--   Actual Eisenstein Cubic: rational Coord Equiv apply
-- statement:
--   The Actual Eisenstein Cubic construction uses the rational Coord Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L229-L233
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L229-L233

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
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

theorem OAI.ActualEisensteinCubic.rationalCoordEquiv_apply (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    rationalCoordEquiv m hm (a,b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b)) := by sorry
