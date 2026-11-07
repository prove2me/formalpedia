-- Prove2me | Theorems.Thm_OAI_GaussianMoment_realGauss_cast
-- name    : OAI.GaussianMoment.realGauss_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:29.166464+00:00
-- url     : https://prove2.me/theorems/ba5b32be-6ab9-45b6-a852-9ab2e2712b9f
-- title:
--   Gaussian Moment: real Gauss cast
-- statement:
--   The Gaussian Moment construction uses the real Gauss cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L326-L332
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L326-L332

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
open OAI.GaussianMoment
open scoped Topology
open Filter

theorem OAI.GaussianMoment.realGauss_cast (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by sorry
