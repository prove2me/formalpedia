-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_pairing_ito_eq_zero
-- name    : LevyStochCalc.Brownian.Ito.pairing_ito_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:53:55.264177+00:00
-- url     : https://prove2.me/theorems/08093c92-66b2-4b7e-9345-9fd78f5a6795
-- title:
--   pairing ito eq zero
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.pairing_ito_eq_zero` is extracted from `LevyStochCalc.Brownian.PRPPairing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing a weight orthogonal to the Itô integrals against a trigonometric increment

If `Z` pairs to zero against every Itô integral, then pairing it against `g (X_t)`, for `X` a
version of `∫ 1_{(a,b]} dW` and `g` one of the scaled trigonometric functions, gives a scalar
function of `t` that solves `Λ(t) = −(l²/2) ∫_0^t 1_{(a,b]}(s) Λ(s) ds`. Grönwall then forces
`Λ` to vanish.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Pairing

variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

variable {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

end Pairing

section Perp

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.pairing_ito_eq_zero (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ}
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, Z ω * V ω * ((stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) ∂P = 0 := by sorry
