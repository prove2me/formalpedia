-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_simpleIntegral_sq_sub_compensator
-- name    : LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:04:52.201423+00:00
-- url     : https://prove2.me/theorems/1662f3c0-357b-4be8-8d4d-f668e3b29ba6
-- title:
--   martingale simpleIntegral sq sub compensator
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionCompensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    MeasureTheory.Martingale
      (fun t ω => (simpleIntegral W G t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
      ℱ P := by sorry
