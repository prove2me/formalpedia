-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_le_integral_add_of_levyProkhorovEDist_lt
-- name    : LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:37:54.897104+00:00
-- url     : https://prove2.me/theorems/b787fa7f-f8fd-4864-9906-27d46b5ee679
-- title:
--   integral le integral add of levyProkhorovEDist lt
-- statement:
--   The source theorem `LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt` is extracted from `LevyStochCalc.Probability.LevyProkhorovLipschitz`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_LevyProkhorovLipschitz_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrals of Lipschitz functions under the Lévy–Prokhorov metric

For probability measures `μ`, `ν` on a pseudo-metric space and a nonnegative bounded continuous
`K`-Lipschitz function `g`,
`|∫ g dμ - ∫ g dν| ≤ (K + ‖g‖) · levyProkhorovDist μ ν`.

By the layer-cake formula, `∫ g dμ` is bounded by the integral over `t ∈ (0, ‖g‖]` of the
`ν`-mass of the `ε`-thickening of `{t ≤ g}`, plus `ε ‖g‖`, whenever the Lévy–Prokhorov distance
is below `ε`. Since `g` is `K`-Lipschitz, that thickening lies inside `{t - K ε ≤ g}`, and shifting
the layer-cake integral by `K ε` costs at most `K ε`.

## Main statements

* `LevyStochCalc.Probability.thickening_setOf_le_subset` — the `ε`-thickening of a superlevel set
  `{t ≤ f}` of a `K`-Lipschitz function lies in `{t - K ε ≤ f}`.
* `LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt` — the one-sided
  bound `∫ g dμ ≤ ∫ g dν + ε (K + ‖g‖)` when `levyProkhorovEDist μ ν < ε`.
* `LevyStochCalc.Probability.abs_integral_sub_integral_le_levyProkhorovDist` — the two-sided
  bound `|∫ g dμ - ∫ g dν| ≤ (K + ‖g‖) · levyProkhorovDist μ ν`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω : Type*} [PseudoMetricSpace Ω]

variable [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

theorem _root_.LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (g : Ω →ᵇ ℝ) {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg_nn : ∀ x, 0 ≤ g x) {ε : ℝ} (hε : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) :
    ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν + ε * (K + ‖g‖) := by sorry
