-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_tensor_poisson
-- name    : OAI.RankTwoPoisson.tensor_poisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:26:12.511955+00:00
-- url     : https://prove2.me/theorems/22ea0e4c-783d-4206-b83a-f153c81e26c9
-- title:
--   Rank Two Poisson: tensor poisson
-- statement:
--   The Rank Two Poisson construction uses the tensor poisson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L529-L543
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L529-L543

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
open OAI.RankTwoPoisson
open Real

theorem OAI.RankTwoPoisson.tensor_poisson (f g : 𝓢(ℝ, ℂ)) :
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
      ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) := by sorry
