-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_measurable_of_ae_eq_of_null_sets
-- name    : LevyStochCalc.Probability.measurable_of_ae_eq_of_null_sets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:06:45.106062+00:00
-- url     : https://prove2.me/theorems/944df990-18bb-4064-b0cf-f4be56514321
-- title:
--   measurable of ae eq of null sets
-- statement:
--   The source theorem `LevyStochCalc.Probability.measurable_of_ae_eq_of_null_sets` is extracted from `LevyStochCalc.Ito.JumpDiffusionAdapted`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F000
import Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Adaptedness of a jump diffusion

The jump-diffusion integral equation of `LevyStochCalc.Ito.Picard.SolvesOn` expresses the path
map at time `t` as the sum of a drift integral over `[0, t]`, a Brownian Itô integral and a
compensated Poisson integral. The Brownian integral is strongly adapted to `ℱ`
(`LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted`), the compensated
integral is adapted to the right-continuation `ℱ₊` of `ℱ`
(`LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted`), and the drift integral of a
progressively measurable integrand is `ℱ t`-measurable
(`ProgressivelyMeasurable.measurable_setIntegral_Icc`), so the right-hand side is
`ℱ₊ t`-measurable and the equation transfers that measurability to the path map up to a null
set.

## Main statements

* `SolvesOn.aeStronglyMeasurable_rightCont` — the path map at time `t` is
  `ℱ₊ t`-a.e.-strongly measurable, given progressive measurability of the drift
  integrand along the path.
* `SolvesOn.stronglyMeasurable_rightCont` — the same with the null set absorbed, when `ℱ 0`
  contains the `P`-null sets and the path map is jointly measurable.
* `SolvesOn.stronglyMeasurable_of_isRegular` — under the usual conditions and the Lipschitz and
  regularity hypotheses on the coefficients, every jointly measurable, `S²`-bounded solution on
  all horizons is `ℱ t`-strongly measurable at every `t ≥ 0`; no hypothesis on the drift
  integrand is needed.
* `JumpDiffusion.stronglyMeasurable_of_solvesOn`, `JumpDiffusion.exists_unique_adapted` — the
  same for a `JumpDiffusion` solving the equation relative to `ℱ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {α : Type*} [MeasurableSpace α]

theorem _root_.LevyStochCalc.Probability.measurable_of_ae_eq_of_null_sets {m₀ m : MeasurableSpace Ω} {P : @Measure Ω m₀}
    {f g : Ω → α} (hnull : ∀ s : Set Ω, MeasurableSet[m₀] s → P s = 0 → MeasurableSet[m] s)
    (hf : Measurable[m₀] f) (hg : Measurable[m] g) (hfg : f =ᵐ[P] g) :
    Measurable[m] f := by sorry
