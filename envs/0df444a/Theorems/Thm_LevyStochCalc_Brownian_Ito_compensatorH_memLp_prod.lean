-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_compensatorH_memLp_prod
-- name    : LevyStochCalc.Brownian.Ito.compensatorH_memLp_prod
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:25:11.873689+00:00
-- url     : https://prove2.me/theorems/7d522ea9-b878-4ece-a232-d1e4a19b8721
-- title:
--   compensatorH memLp prod
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.compensatorH_memLp_prod` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionQuadVar`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

include h_meas h_sq_int_global in
omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.compensatorH_memLp_prod {t : ℝ} (ht : 0 < t) :
    MeasureTheory.MemLp (fun p : Ω × ℝ => H p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by sorry
