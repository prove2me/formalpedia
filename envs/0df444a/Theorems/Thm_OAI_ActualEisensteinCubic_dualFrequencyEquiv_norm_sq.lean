-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_dualFrequencyEquiv_norm_sq
-- name    : OAI.ActualEisensteinCubic.dualFrequencyEquiv_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:28.477387+00:00
-- url     : https://prove2.me/theorems/577bf935-be85-4918-b5fb-9e82e75d5bad
-- title:
--   Actual Eisenstein Cubic: dual Frequency Equiv norm sq
-- statement:
--   The Actual Eisenstein Cubic construction uses the dual Frequency Equiv norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L287-L292
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L287-L292

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

theorem OAI.ActualEisensteinCubic.dualFrequencyEquiv_norm_sq (k l : ℤ) :
    ‖eisEmbedding (dualFrequencyEquiv (k,l))‖ ^ 2 =
      (((k^2+k*l+l^2 : ℤ) : ℝ)) := by sorry
