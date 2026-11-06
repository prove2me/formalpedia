-- Prove2me | Theorems.Thm_OAI_SevenEighths_Continuation_vertical_integral_eq_of_horizontal_vanish
-- name    : OAI.SevenEighths.Continuation.vertical_integral_eq_of_horizontal_vanish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:37.111593+00:00
-- url     : https://prove2.me/theorems/a8ec5e5e-d298-47a6-b8dc-1064824e6a81
-- title:
--   Continuation: vertical integral eq of horizontal vanish
-- statement:
--   The Continuation construction uses the vertical integral eq of horizontal vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ContinuationContour.lean#L12-L41
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ContinuationContour.lean#L12-L41

import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationContour
set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation

theorem OAI.SevenEighths.Continuation.vertical_integral_eq_of_horizontal_vanish (F : ℂ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (ha : Integrable (fun y : ℝ => F ((a : ℂ) + y * I)))
    (hb : Integrable (fun y : ℝ => F ((b : ℂ) + y * I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I))
      atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by sorry
