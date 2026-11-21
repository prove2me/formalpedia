-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_sub_sq_bochner_clamped_weighted
-- name    : LevyStochCalc.Brownian.Ito.simpleIntegral_sub_sq_bochner_clamped_weighted
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:06:20.539655+00:00
-- url     : https://prove2.me/theorems/b4068488-057b-4772-9b05-c7d6b12e9e29
-- title:
--   simpleIntegral sub sq bochner clamped weighted
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_sub_sq_bochner_clamped_weighted` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionCompensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionCompensator_F001

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

theorem _root_.LevyStochCalc.Brownian.Ito.simpleIntegral_sub_sq_bochner_clamped_weighted
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ s) g)
    {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
    ∫ ω, g ω * (simpleIntegral W H t ω - simpleIntegral W H s ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (max s (min (H.partition i.succ) t) - max s (min (H.partition i.castSucc) t))
          * ∫ ω, g ω * (H.ξ i ω) ^ 2 ∂P := by sorry
