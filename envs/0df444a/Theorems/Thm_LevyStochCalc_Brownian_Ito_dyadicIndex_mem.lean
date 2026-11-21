-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_dyadicIndex_mem
-- name    : LevyStochCalc.Brownian.Ito.dyadicIndex_mem
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T10:11:10.555711+00:00
-- url     : https://prove2.me/theorems/c982d4af-6f7f-439c-a3f2-b604a9ca11d2
-- title:
--   dyadicIndex mem
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.dyadicIndex_mem` is extracted from `LevyStochCalc.Brownian.ItoDensityShiftedAverages`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F002

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

theorem _root_.LevyStochCalc.Brownian.Ito.dyadicIndex_mem (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
    (hs : 0 < s ∧ s ≤ T) :
    ((dyadicIndex n T hT s hs : ℕ) : ℝ) * T / (2 ^ n : ℕ) < s ∧
    s ≤ (((dyadicIndex n T hT s hs : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by sorry
