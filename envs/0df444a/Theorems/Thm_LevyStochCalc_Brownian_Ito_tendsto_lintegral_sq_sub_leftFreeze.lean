-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_lintegral_sq_sub_leftFreeze
-- name    : LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_sub_leftFreeze
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:29:31.355866+00:00
-- url     : https://prove2.me/theorems/fa64c1a3-1d9b-4896-b41c-a02ad5d0d6f0
-- title:
--   tendsto lintegral sq sub leftFreeze
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_sub_leftFreeze` is extracted from `LevyStochCalc.Brownian.LeftFreeze`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_eval_mul_sq_lt_top
import Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F001
import Definitions.Def_SourceProof_ab7ca2049b8b9b3eaf1b7768

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Freezing a bounded adapted process at the left endpoints of a dyadic grid

Freezing a bounded adapted process `Y` at the left endpoints of the dyadic partition of `[0, t]`
of level `n` (`Analysis/DyadicGrid.lean`) gives a simple predictable integrand
`leftFreeze Y t n`, whose value at a time `s ∈ (0, t]` is `Y` at the left endpoint `leftPt t n s`
of the cell containing `s`. When the
frozen values converge, at every positive time and almost every sample point, to a bounded
process `Y₋`, the Itô integrals of `leftFreeze Y t n · H` converge in `L²` to the Itô integral of
`Y₋ · H`, by the difference isometry and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

open LevyStochCalc.Analysis

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Freeze

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t) (n : ℕ)

end Freeze

section Limit

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s)) {t : ℝ} (ht : 0 < t)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_sub_leftFreeze (Yminus : ℝ → Ω → ℝ)
    (hYmb : ∀ s ω, |Yminus s ω| ≤ C)
    (hmm' : Measurable (Function.uncurry fun ω s => Yminus s ω * H ω s))
    (hmp' : Probability.ProgressivelyMeasurable ℱ fun ω s => Yminus s ω * H ω s)
    (hmq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hconv : ∀ᵐ ω ∂P, ∀ s, 0 < s → s ≤ t →
      Tendsto (fun n : ℕ => Y (leftPt t n s) ω) atTop (𝓝 (Yminus s ω))) :
    Tendsto (fun n : ℕ => ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (leftFreeze Y hYb hYm ht n).eval s ω * H ω s)
        ((leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm)
        ((leftFreeze Y hYb hYm ht n).progressivelyMeasurable_eval_mul ℱ
          (leftFreeze_adapt Y hYb hYm ht n ℱ hYad) hp)
        ((leftFreeze Y hYb hYm ht n).lintegral_eval_mul_sq_lt_top hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq' t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by sorry
