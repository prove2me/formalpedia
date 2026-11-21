-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_pow_four_le
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:56:54.85818+00:00
-- url     : https://prove2.me/theorems/2f778a7c-229f-4265-9879-f6390ae3132c
-- title:
--   integral partialSum pow four le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le` is extracted from `LevyStochCalc.Brownian.ItoFourthMomentPartialSums`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second and fourth moments of the elementary Brownian integral

The moment recursion over the partial sums of the elementary integral of a simple integrand: one
step adds the second moment of the new tile, and in the fourth-moment recursion the odd-power
cross terms drop out because a coefficient measurable before an increment is independent of it.
Iterating gives `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·C⁴·T²` for an integrand bounded by `C`, where `c` is
the fourth moment of the standard Gaussian, and the sharper form
`𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·(∑_j c_j² Δ_j)²` against a per-tile coefficient bound `c`, which for a
coefficient vanishing off a subinterval sees only that subinterval's length.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

section Moments

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)

include hℱ h_adapt hC0 hC in

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le : ∀ (k : ℕ) (hk : k ≤ G.N),
    ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
      ≤ 6 * C ^ 4 * (G.partition (Fin.last G.N)
          * G.partition ⟨k, Nat.lt_succ_of_le hk⟩)
        + gaussianFourthMoment * C ^ 4 * G.partition ⟨k, Nat.lt_succ_of_le hk⟩ ^ 2 := by sorry
