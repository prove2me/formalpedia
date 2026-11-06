-- Prove2me | Theorems.Thm_OAI_FixedRayActiveSet_product_sum_by_active_set
-- name    : OAI.FixedRayActiveSet.product_sum_by_active_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:24.894855+00:00
-- url     : https://prove2.me/theorems/17ff8f21-9bfb-4e09-bffd-37b90f73eeae
-- title:
--   Fixed Ray Active Set: product sum by active set
-- statement:
--   The Fixed Ray Active Set construction uses the product sum by active set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L338-L358
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L338-L358

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

theorem OAI.FixedRayActiveSet.product_sum_by_active_set
    {ι : Type*} [Fintype ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (f : ∀ i, F i → ℂ) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ (Finset.univ : Finset ι).powerset,
        (∏ i ∈ A, ∑ u : (F i)ˣ, f i (u : F i)) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by sorry
