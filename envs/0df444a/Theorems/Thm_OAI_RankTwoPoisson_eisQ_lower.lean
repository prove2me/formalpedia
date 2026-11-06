-- Prove2me | Theorems.Thm_OAI_RankTwoPoisson_eisQ_lower
-- name    : OAI.RankTwoPoisson.eisQ_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:32.353566+00:00
-- url     : https://prove2.me/theorems/0e0656e1-ae24-4e73-a511-4a553f8351d2
-- title:
--   Rank Two Poisson: eis Q lower
-- statement:
--   The Rank Two Poisson construction uses the eis Q lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L595-L598
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L595-L598

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

theorem OAI.RankTwoPoisson.eisQ_lower (z : ℤ × ℤ) :
    ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 2 ≤ eisQ z := by sorry
