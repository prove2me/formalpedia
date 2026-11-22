-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_stochasticIntegralBrownian_sum_univ
-- name    : LevyStochCalc.Ito.JumpFormula.stochasticIntegralBrownian_sum_univ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:42:40.873174+00:00
-- url     : https://prove2.me/theorems/1ff98b56-6b50-4f88-b1b9-959c198b4527
-- title:
--   stochasticIntegralBrownian sum univ
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.stochasticIntegralBrownian_sum_univ` is extracted from `LevyStochCalc.Ito.FiniteActivityMixed`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F001
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity Itô–Lévy identity along a truncated path, in the mixed form

Along a càdlàg path `y` that is a continuous vector Itô process plus the left-limit jump sum of
a jump diffusion `X` over a mark set of finite intensity, the increment of a `C²` state function
with bounded derivatives is the mixed drift integral, the Brownian integral of the mixed
diffusion integrand, the compensated integral of the mixed jump increment over the mark set and
the compensator-drift integral over that set. The derivatives of the state function are read
along `y` and the coefficients along `X`.

The proof telescopes Itô's formula for the time-augmented continuous part between consecutive
arrival times of the mark set, identifies the increments across the arrival times with the
atom sum of the mixed jump increment read at the left limits, and identifies that atom sum with
the pathwise form of the compensated integral.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section BrownianSum

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Ito.JumpFormula.stochasticIntegralBrownian_sum_univ {T : ℝ} (hT : 0 < T) : ∀ {m : ℕ}
    (H : Fin m → Ω → ℝ → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : Fin m) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hms : Measurable (Function.uncurry fun ω s => ∑ i, H i ω s))
    (hps : Probability.ProgressivelyMeasurable ℱ fun ω s => ∑ i, H i ω s)
    (hqs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖∑ i, H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => ∑ i, H i ω s) hms hps hqs T
      =ᵐ[P] fun ω => ∑ i, stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by sorry
