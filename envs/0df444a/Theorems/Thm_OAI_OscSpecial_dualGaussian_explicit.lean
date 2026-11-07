-- Prove2me | Theorems.Thm_OAI_OscSpecial_dualGaussian_explicit
-- name    : OAI.OscSpecial.dualGaussian_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:29.528251+00:00
-- url     : https://prove2.me/theorems/f924715b-e03a-45f3-8e9e-6e2e920bc304
-- title:
--   Osc Special: dual Gaussian explicit
-- statement:
--   The Osc Special construction uses the dual Gaussian explicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L75-L94
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L75-L94

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
open OAI.OscSpecial

theorem OAI.OscSpecial.dualGaussian_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      Complex.exp (-(Real.pi : ℂ) *
        (((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
          ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
         Complex.I / (2 * (r η a b : ℂ)) *
          (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
            2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
            (b : ℂ) * (z.2 : ℂ) ^ 2))) := by sorry
