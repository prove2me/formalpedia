-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_dyadicAvg_brownian_bounded
-- name    : LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_bounded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:07:00.993701+00:00
-- url     : https://prove2.me/theorems/f1fa887b-3f0d-4da8-a027-1180938d1c30
-- title:
--   dyadicAvg brownian bounded
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_bounded` is extracted from `LevyStochCalc.Brownian.ItoDensityDyadicAverages`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).

omit [MeasurableSpace Ω] in

theorem _root_.LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_bounded
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvg_brownian (T := T) g n i ω| ≤ M := by sorry
