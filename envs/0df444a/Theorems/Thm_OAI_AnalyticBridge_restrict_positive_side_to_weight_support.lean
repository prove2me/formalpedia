-- Prove2me | Theorems.Thm_OAI_AnalyticBridge_restrict_positive_side_to_weight_support
-- name    : OAI.AnalyticBridge.restrict_positive_side_to_weight_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:40.182224+00:00
-- url     : https://prove2.me/theorems/ce3f553d-4f6c-493c-98fd-b41c44b563b1
-- title:
--   Analytic Bridge: restrict positive side to weight support
-- statement:
--   The Analytic Bridge construction uses the restrict positive side to weight support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L299-L307
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L299-L307

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
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
open OAI.AnalyticBridge

theorem OAI.AnalyticBridge.restrict_positive_side_to_weight_support
    {Ω : Type*} (S : Finset Ω) (w : Ω → ℂ) (U : Ω → ℂ) :
    (∑ ω ∈ S with w ω ≠ 0, ‖w ω‖ * ‖U ω‖ ^ 2) =
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) := by sorry
