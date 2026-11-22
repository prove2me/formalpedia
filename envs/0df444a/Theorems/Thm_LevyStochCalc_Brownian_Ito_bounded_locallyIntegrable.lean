-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_bounded_locallyIntegrable
-- name    : LevyStochCalc.Brownian.Ito.bounded_locallyIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T09:44:55.515619+00:00
-- url     : https://prove2.me/theorems/15df0857-afff-47dc-91ac-46f89d609609
-- title:
--   bounded locallyIntegrable
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.bounded_locallyIntegrable` is extracted from `LevyStochCalc.Brownian.ItoDensityShiftedAverages`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F001

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

theorem _root_.LevyStochCalc.Brownian.Ito.bounded_locallyIntegrable
    (g : ℝ → ℝ) (h_meas : Measurable g) (M : ℝ) (h_bound : ∀ s, |g s| ≤ M) :
    MeasureTheory.LocallyIntegrable g volume := by sorry
