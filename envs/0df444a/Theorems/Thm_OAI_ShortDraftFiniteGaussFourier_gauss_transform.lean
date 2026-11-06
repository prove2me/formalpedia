-- Prove2me | Theorems.Thm_OAI_ShortDraftFiniteGaussFourier_gauss_transform
-- name    : OAI.ShortDraftFiniteGaussFourier.gauss_transform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:28.13681+00:00
-- url     : https://prove2.me/theorems/0da472aa-94d0-4842-8b59-8998a1887106
-- title:
--   Short Draft Finite Gauss Fourier: gauss transform
-- statement:
--   The Short Draft Finite Gauss Fourier construction uses the gauss transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L21-L33
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L21-L33

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

theorem OAI.ShortDraftFiniteGaussFourier.gauss_transform (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ x : F, χ x * ψ (h * x)) =
      if h = 0 then 0 else (χ h)⁻¹ * gaussSum χ ψ := by sorry
