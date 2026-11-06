-- Prove2me | Theorems.Thm_OAI_FixedRayActiveSet_admissible_branch_count
-- name    : OAI.FixedRayActiveSet.admissible_branch_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:29.916199+00:00
-- url     : https://prove2.me/theorems/c2d754d4-2ff8-4ebd-843a-088cb5319ec9
-- title:
--   Fixed Ray Active Set: admissible branch count
-- statement:
--   The Fixed Ray Active Set construction uses the admissible branch count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L370-L378
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L370-L378

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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
open OAI.FixedRayActiveSet
open scoped BigOperators

theorem OAI.FixedRayActiveSet.admissible_branch_count
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι → ℕ) :
    ((Finset.univ : Finset ι).powerset.filter
      (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)).card
      ≤ 2 ^ Fintype.card ι := by sorry
