-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_lintegral_sq
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:25:01.720183+00:00
-- url     : https://prove2.me/theorems/7a78c1b5-b90d-4bc2-9896-6315c160fc35
-- title:
--   stochasticIntegralBrownian lintegral sq
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionQuadVar`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: isometry, right continuity and quadratic variation

The `L²`-isometry `∫⁻ ‖stochasticIntegralBrownian T‖₊² = ∫⁻ ∫⁻_{[0, T]} ‖H‖₊²`,
membership of the process in `L²(P)`, right `L²`-continuity of its time slices and
the resulting martingale property with respect to the right-continuation `ℱ₊` of
`ℱ`, and the compensator `∫_{[0, t]} (H ω u)² du` with the `ℱ`-martingale property
of the compensated square.
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

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
