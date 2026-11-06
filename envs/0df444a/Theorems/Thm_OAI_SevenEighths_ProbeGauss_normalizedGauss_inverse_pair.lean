-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGauss_normalizedGauss_inverse_pair
-- name    : OAI.SevenEighths.ProbeGauss.normalizedGauss_inverse_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:40:54.641902+00:00
-- url     : https://prove2.me/theorems/f04f2f84-3fc3-4ce2-85e7-c97102d720fc
-- title:
--   Probe Gauss: normalized Gauss inverse pair
-- statement:
--   The Probe Gauss construction uses the normalized Gauss inverse pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L60-L68
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L60-L68

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

theorem OAI.SevenEighths.ProbeGauss.normalizedGauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss χ⁻¹ ψ = χ (-1) := by sorry
