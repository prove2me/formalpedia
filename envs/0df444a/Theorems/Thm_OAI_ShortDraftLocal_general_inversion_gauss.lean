-- Prove2me | Theorems.Thm_OAI_ShortDraftLocal_general_inversion_gauss
-- name    : OAI.ShortDraftLocal.general_inversion_gauss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:29.321934+00:00
-- url     : https://prove2.me/theorems/76ff208e-94f2-4254-9fe4-05c81b6ec391
-- title:
--   Short Draft Local: general inversion gauss
-- statement:
--   The Short Draft Local construction uses the general inversion gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L73-L95
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L73-L95

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
open OAI.ShortDraftLocal
open AddChar MulChar

theorem OAI.ShortDraftLocal.general_inversion_gauss {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (a : F) :
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by sorry
