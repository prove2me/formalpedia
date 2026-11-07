-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_dual_gaussian_is_actual_trace_phase
-- name    : OAI.ActualEisensteinCubic.dual_gaussian_is_actual_trace_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:18.967226+00:00
-- url     : https://prove2.me/theorems/cb11f7a4-f2e3-428a-9ed2-3f3a7fefe071
-- title:
--   Actual Eisenstein Cubic: dual gaussian is actual trace phase
-- statement:
--   The Actual Eisenstein Cubic construction uses the dual gaussian is actual trace phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L372-L403
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L372-L403

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

theorem OAI.ActualEisensteinCubic.dual_gaussian_is_actual_trace_phase
    (a b k l : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (k,l) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      ShortDraftTrace.breveE
        (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by sorry
