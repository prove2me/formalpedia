-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_rational_quadratic_phase
-- name    : OAI.ActualEisensteinCubic.rational_quadratic_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:21:58.616148+00:00
-- url     : https://prove2.me/theorems/2d0c8715-84c0-4f34-9a19-8500ca9c24d2
-- title:
--   Actual Eisenstein Cubic: rational quadratic phase
-- statement:
--   The Actual Eisenstein Cubic construction uses the rational quadratic phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L235-L262
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L235-L262

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

theorem OAI.ActualEisensteinCubic.rational_quadratic_phase (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    letI : NeZero m := ⟨hm⟩
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      breveE_period_coordinates (m : O) (by exact_mod_cast hm)
    ψ ((rationalCoordEquiv m hm (a,b)) ^ 2) =
      ZMod.stdAddChar (2*a*b - b^2) := by sorry
