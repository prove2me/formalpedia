-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_isometry_stochasticIntegralBrownian
-- name    : LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:25:30.201528+00:00
-- url     : https://prove2.me/theorems/532067c0-2619-424e-83da-4beb02afb70f
-- title:
--   The L² isometry for Brownian stochastic integration
-- statement:
--   For a Brownian motion with a compatible filtration, a measurable and progressively measurable real integrand H with finite squared energy on every positive bounded horizon, and $T>0$, the integral over ω of the square of the Brownian stochastic integral at T equals the integral over ω and time in $[0,T]$ of the squared integrand. The conclusion uses the source ENNReal integrals and original stochastic-integral definition.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc/blob/main/LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean

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

theorem _root_.LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
