-- Prove2me | Theorems.Thm_OAI_FixedRayActiveSet_branch_zero_of_local_mask
-- name    : OAI.FixedRayActiveSet.branch_zero_of_local_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:34.13721+00:00
-- url     : https://prove2.me/theorems/37fd7686-4da8-4b24-a3fa-31a60b10a6d4
-- title:
--   Fixed Ray Active Set: branch zero of local mask
-- statement:
--   The Fixed Ray Active Set construction uses the branch zero of local mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L360-L368
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L360-L368

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

theorem OAI.FixedRayActiveSet.branch_zero_of_local_mask
    {ι : Type*} [DecidableEq ι] (I A : Finset ι)
    (scalar dual inactive : ι → ℂ)
    (i : ι) (hi : i ∈ A) (hzero : dual i = 0) :
    (∏ k ∈ A, scalar k * dual k) *
      (∏ k ∈ I \ A, inactive k) = 0 := by sorry
