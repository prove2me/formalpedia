-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_dyadicAvg_brownian_eq_average_closedBall
-- name    : LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_eq_average_closedBall
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:46:34.457189+00:00
-- url     : https://prove2.me/theorems/3fd069c5-fbc2-472b-acb9-5633207fd552
-- title:
--   dyadicAvg brownian eq average closedBall
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_eq_average_closedBall` is extracted from `LevyStochCalc.Brownian.ItoDensityShiftedAverages`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable.

-- `omit` the unused `[MeasurableSpace Ω]` section variable.

omit [MeasurableSpace Ω] in

theorem _root_.LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_eq_average_closedBall
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    dyadicAvg_brownian (T := T) g n i ω =
      ⨍ y in Metric.closedBall
        ((dyadicPartition_brownian T n i.castSucc + dyadicPartition_brownian T n i.succ) / 2)
        ((dyadicPartition_brownian T n i.succ - dyadicPartition_brownian T n i.castSucc) / 2),
        g ω y ∂volume := by sorry
