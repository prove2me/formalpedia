-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_mul_stochasticIntegralBrownian_hitInd
-- name    : LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:22:43.91674+00:00
-- url     : https://prove2.me/theorems/fc3e3f69-a1ea-45fb-ab51-e4a894304bcc
-- title:
--   mul stochasticIntegralBrownian hitInd
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd` is extracted from `LevyStochCalc.Ito.ItoFormulaShift`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaShift_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a translated function

Translating the argument of a twice continuously differentiable function by a fixed vector
translates its Fréchet derivatives and its partial derivatives by the same vector, so Itô's
formula along a stopped path holds for the translate with every derivative read at the
translated path.

A weight that is known at a deterministic time and vanishes off the event that a stopping time
equals that time passes inside the Itô integral of an integrand that vanishes up to that
stopping time: the integrand is then carried by the window between that time and the horizon,
and the increment removed by the window is invisible on the event.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_shift` — Itô's formula along a stopped path for
  a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd` — a bounded weight known at
  a deterministic time, cut to the event that a stopping time equals it, passes inside the Itô
  integral of an integrand vanishing up to that stopping time.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd_stopped_sub` — the same for
  the increment of an integrand between two stopping times.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Translate

variable {n : ℕ}

end Translate

section ShiftedFormula

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end ShiftedFormula

section StoppedIncrement

variable {Ω : Type u}

end StoppedIncrement

section HitIndPullOut

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    {D : Ω → ℝ → ℝ} (hmD : Measurable (Function.uncurry D))
    (hpD : Probability.ProgressivelyMeasurable ℱ D)
    (hqD : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hD0 : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ σ ω → D ω s = 0)
    (hwm : Measurable (Function.uncurry fun ω s => hitInd σ a ω * V ω * D ω s))
    (hwp : Probability.ProgressivelyMeasurable ℱ fun ω s => hitInd σ a ω * V ω * D ω s)
    (hwq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖hitInd σ a ω * V ω * D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    (fun ω => hitInd σ a ω * V ω
        * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD T ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω * D ω s) hwm hwp hwq T := by sorry
