-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_actual_oscillatory_binary_coordinate
-- name    : OAI.ActualEisensteinCubic.actual_oscillatory_binary_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:22.362728+00:00
-- url     : https://prove2.me/theorems/80677db1-7c3b-4d48-96cc-bb54ff04c6c9
-- title:
--   Actual Eisenstein Cubic: actual oscillatory binary coordinate
-- statement:
--   The Actual Eisenstein Cubic construction uses the actual oscillatory binary coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L204-L228
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L204-L228

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex

theorem OAI.ActualEisensteinCubic.actual_oscillatory_binary_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (m,n) := by sorry
