-- Prove2me | Theorems.Thm_OAI_RankTwoLimit_dual_sum_tendsto_one_small_t
-- name    : OAI.RankTwoLimit.dual_sum_tendsto_one_small_t
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:45:31.648045+00:00
-- url     : https://prove2.me/theorems/8ec93a87-f581-48dc-b5a3-d89ed16e8b30
-- title:
--   Rank Two Limit: dual sum tendsto one small t
-- statement:
--   The Rank Two Limit construction uses the dual sum tendsto one small t property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L566-L573
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L566-L573

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
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
open OAI.RankTwoLimit
open scoped Topology
open Filter

theorem OAI.RankTwoLimit.dual_sum_tendsto_one_small_t (x y : ℝ) :
    Tendsto (fun t : ℝ => ∑' z : ℤ × ℤ, dualTerm (4 / (3 * t)) x y z)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by sorry
