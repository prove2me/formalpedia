-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_product_defect_le
-- name    : OAI.SevenEighths.ProbeEuler.product_defect_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:52:44.343857+00:00
-- url     : https://prove2.me/theorems/0c85e852-a5a0-47f5-8dd9-32708a644861
-- title:
--   Probe Euler: product defect le
-- statement:
--   The Probe Euler construction uses the product defect le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L50-L56
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L50-L56

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

theorem OAI.SevenEighths.ProbeEuler.product_defect_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2)
    (hsmall : (∑' i, b i) ≤ 1/6) : ‖(∏' i, F i)-1‖ ≤ 1/2 := by sorry
