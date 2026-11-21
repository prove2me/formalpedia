-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_fiber_sum_telescope_clamped
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.fiber_sum_telescope_clamped
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:02:14.080024+00:00
-- url     : https://prove2.me/theorems/c08b12d4-acf2-44e9-9a11-86d307e0cad7
-- title:
--   fiber sum telescope clamped
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.fiber_sum_telescope_clamped` is extracted from `LevyStochCalc.Brownian.SimplePredictableRefineInvariance`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.fiber_sum_telescope_clamped
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    (h_refines : ∀ i : Fin (H.N + 1), ∃ k : Fin (M + 1), π' k = H.partition i)
    (i : Fin H.N) (ω : Ω) (t : ℝ) :
    (∑ j ∈ (Finset.univ : Finset (Fin M)).filter (fun j => idxMap j = i),
        H.ξ (idxMap j) ω
          * (W.W (min (π' j.succ) t) ω - W.W (min (π' j.castSucc) t) ω))
      = H.ξ i ω
          * (W.W (min (H.partition i.succ) t) ω
              - W.W (min (H.partition i.castSucc) t) ω) := by sorry
