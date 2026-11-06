-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_product_eq_exp_log
-- name    : OAI.SevenEighths.ProbeEuler.product_eq_exp_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:27.29805+00:00
-- url     : https://prove2.me/theorems/8ccdf557-031a-40fd-be23-d0bc0fb124b8
-- title:
--   Probe Euler: product eq exp log
-- statement:
--   The Probe Euler construction uses the product eq exp log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L29-L37
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L29-L37

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

theorem OAI.SevenEighths.ProbeEuler.product_eq_exp_log {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    (∏' i, F i) = Complex.exp (∑' i, Complex.log (F i)) := by sorry
