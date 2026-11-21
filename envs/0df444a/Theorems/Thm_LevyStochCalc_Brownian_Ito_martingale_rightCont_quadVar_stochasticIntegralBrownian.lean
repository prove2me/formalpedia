-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_rightCont_quadVar_stochasticIntegralBrownian
-- name    : LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:28:54.211609+00:00
-- url     : https://prove2.me/theorems/96b29db4-26ed-4bcc-b006-e8930d4a305c
-- title:
--   martingale rightCont quadVar stochasticIntegralBrownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionApi`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002

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

include h_meas h_progMeas h_sq_int_global hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ.rightCont P := by sorry
