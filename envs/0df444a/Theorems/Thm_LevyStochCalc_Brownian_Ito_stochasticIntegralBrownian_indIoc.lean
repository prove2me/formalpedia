-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indIoc
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indIoc
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:51:50.18217+00:00
-- url     : https://prove2.me/theorems/2bde9fd8-2cfa-4220-93fb-41b3db4d5920
-- title:
--   stochasticIntegralBrownian indIoc
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indIoc` is extracted from `LevyStochCalc.Brownian.ItoIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô integral of an indicator is a Brownian increment

The integrand `1_{(a, b]}` is simple, so its `L²` Itô integral up to a time `t` is the elementary
integral `W_{b ∧ t} − W_{a ∧ t}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Indicator

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indIoc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hm : Measurable (Function.uncurry (indIoc Ω a b)))
    (hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b))
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq t
      =ᵐ[P] fun ω => W.W (min b t) ω - W.W (min a t) ω := by sorry
