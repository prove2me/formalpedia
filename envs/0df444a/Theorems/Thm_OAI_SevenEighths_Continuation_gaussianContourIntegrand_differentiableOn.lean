-- Prove2me | Theorems.Thm_OAI_SevenEighths_Continuation_gaussianContourIntegrand_differentiableOn
-- name    : OAI.SevenEighths.Continuation.gaussianContourIntegrand_differentiableOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:52:28.335202+00:00
-- url     : https://prove2.me/theorems/92a865f9-c907-4838-befb-fe6338b0a3c6
-- title:
--   Continuation: gaussian Contour Integrand differentiable On
-- statement:
--   The Continuation construction uses the gaussian Contour Integrand differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ContinuationContour.lean#L100-L107
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ContinuationContour.lean#L100-L107

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

theorem OAI.SevenEighths.Continuation.gaussianContourIntegrand_differentiableOn {G : ℂ → ℂ} {U : Set ℂ}
    (hG : DifferentiableOn ℂ G U) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    DifferentiableOn ℂ (gaussianContourIntegrand G c Z) U := by sorry
