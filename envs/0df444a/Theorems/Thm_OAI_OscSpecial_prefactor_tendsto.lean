-- Prove2me | Theorems.Thm_OAI_OscSpecial_prefactor_tendsto
-- name    : OAI.OscSpecial.prefactor_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:34.929795+00:00
-- url     : https://prove2.me/theorems/b5e55ae8-ca92-4636-b2a7-eac5d18a0833
-- title:
--   Osc Special: prefactor tendsto
-- statement:
--   The Osc Special construction uses the prefactor tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L492-L518
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L492-L518

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
open scoped Topology
open Filter

theorem OAI.OscSpecial.prefactor_tendsto {a b : ℝ} (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) := by sorry
