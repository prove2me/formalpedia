-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGauss_finite_gauss_convolution
-- name    : OAI.SevenEighths.ProbeGauss.finite_gauss_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:40:54.131542+00:00
-- url     : https://prove2.me/theorems/7c3fb5fc-4662-485d-9cfe-bc452ac31855
-- title:
--   Probe Gauss: finite gauss convolution
-- statement:
--   The Probe Gauss construction uses the finite gauss convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L70-L110
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L70-L110

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

theorem OAI.SevenEighths.ProbeGauss.finite_gauss_convolution {F : Type*} [Field F] [Fintype F]
    (χ ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    (∑ d : F, χ d * frequencyGauss ξ ψ (h - d)) =
      χ⁻¹ (-1) * gaussSum χ ψ * frequencyGauss (ξ * χ⁻¹) ψ h := by sorry
