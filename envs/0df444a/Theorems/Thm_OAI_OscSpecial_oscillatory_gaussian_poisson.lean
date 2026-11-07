-- Prove2me | Theorems.Thm_OAI_OscSpecial_oscillatory_gaussian_poisson
-- name    : OAI.OscSpecial.oscillatory_gaussian_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:12.155914+00:00
-- url     : https://prove2.me/theorems/7142aeea-62d8-4f92-b0ac-786bc67a72f1
-- title:
--   Osc Special: oscillatory gaussian poisson
-- statement:
--   The Osc Special construction uses the oscillatory gaussian poisson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L22-L37
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L22-L37

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

theorem OAI.OscSpecial.oscillatory_gaussian_poisson {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian (A η a b) (B η a b) (D η a b) z) =
      (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ,
          RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z := by sorry
