-- Prove2me | Theorems.Thm_OAI_ShortDraftFiniteGaussFourier_product_gauss_transform
-- name    : OAI.ShortDraftFiniteGaussFourier.product_gauss_transform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:34:42.015199+00:00
-- url     : https://prove2.me/theorems/3b91a802-5cd3-4eae-a7c2-02dccbc5f99e
-- title:
--   Short Draft Finite Gauss Fourier: product gauss transform
-- statement:
--   The Short Draft Finite Gauss Fourier construction uses the product gauss transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L35-L51
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L35-L51

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
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
open OAI.ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]

theorem OAI.ShortDraftFiniteGaussFourier.product_gauss_transform
    {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, Field (E i)] [∀ i, Fintype (E i)]
    (χ : ∀ i, MulChar (E i) ℂ) (ψ : ∀ i, AddChar (E i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : ∀ i, E i) :
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
      ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by sorry
