-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_norm_log_sum_le
-- name    : OAI.SevenEighths.ProbeEuler.norm_log_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:22:46.444378+00:00
-- url     : https://prove2.me/theorems/30b05157-1179-4526-b266-a64bc4f554cd
-- title:
--   Probe Euler: norm log sum le
-- statement:
--   The Probe Euler construction uses the norm log sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L39-L48
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean#L39-L48

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

theorem OAI.SevenEighths.ProbeEuler.norm_log_sum_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    ‖∑' i, Complex.log (F i)‖ ≤ (3/2:ℝ) * ∑' i, b i := by sorry
