-- Prove2me | Theorems.Thm_OAI_FixedRayActiveSet_assemble_local_A5
-- name    : OAI.FixedRayActiveSet.assemble_local_A5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:23.471489+00:00
-- url     : https://prove2.me/theorems/e3536c3f-5997-4cc9-a24e-6ef8cf4d9683
-- title:
--   Fixed Ray Active Set: assemble local A5
-- statement:
--   The Fixed Ray Active Set construction uses the assemble local A5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L395-L429
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L395-L429

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

theorem OAI.FixedRayActiveSet.assemble_local_A5
    {ι : Type*} [Fintype ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (j : ι → ℕ) (f : ∀ i, F i → ℂ)
    (scalar dual : ι → ℂ)
    (hzero : ∀ i, j i ≠ 0 → f i 0 = 0)
    (hactive : ∀ i, (∑ u : (F i)ˣ, f i (u : F i)) =
      scalar i * dual i) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, scalar i * dual i) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by sorry
