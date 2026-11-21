-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_lintegral_nnnorm_sq_of_eLpNorm
-- name    : LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:37:36.636191+00:00
-- url     : https://prove2.me/theorems/26f3b8af-4292-46a5-8497-eb4b6651d0dc
-- title:
--   tendsto lintegral nnnorm sq of eLpNorm
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionApi`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The martingale property of the compensated square for the right-continuation `ℱ₊` of `ℱ`,
the unified existence theorem `itoIsometry_brownian_unified_existence` combining the
martingale, quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end MasterSequence

theorem _root_.LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
    {β : Type*} [MeasurableSpace β] {μ : MeasureTheory.Measure β}
    {ι : Type*} {l : Filter ι} {gₙ : ι → β → ℝ} {g : β → ℝ}
    (hgₙ : ∀ n, MeasureTheory.AEStronglyMeasurable (gₙ n) μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ)
    (hgfin : MeasureTheory.eLpNorm g 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x, (‖gₙ n x‖₊ : ℝ≥0∞) ^ 2 ∂μ) l
      (nhds (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ)) := by sorry
