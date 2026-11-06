-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_normalProduct_analytic
-- name    : OAI.SevenEighths.ProbeEuler.normalProduct_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:52:46.981077+00:00
-- url     : https://prove2.me/theorems/d62b4bba-447a-4669-a281-7403f6610b4c
-- title:
--   Probe Euler: normal Product analytic
-- statement:
--   The Probe Euler construction uses the normal Product analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L58-L76
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L58-L76

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_NormalProduct
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler

theorem OAI.SevenEighths.ProbeEuler.normalProduct_analytic {ι : Type*} (F : ι → ℂ → ℂ) (b : ι → ℝ)
    (U : Set ℂ) (hU : IsOpen U) (hb : Summable b)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (hbound : ∀ i s, s ∈ U → ‖F i s-1‖ ≤ b i)
    (hhalf : ∀ i, b i ≤ 1/2) :
    AnalyticOnNhd ℂ (fun s => ∏' i, F i s) U := by sorry
