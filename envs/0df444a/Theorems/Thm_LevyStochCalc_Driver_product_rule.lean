-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_product_rule
-- name    : LevyStochCalc.Driver.product_rule
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:25:00.456705+00:00
-- url     : https://prove2.me/theorems/9d4ce8ec-5fe5-4264-bbed-0f810e9dcbf1
-- title:
--   product rule
-- statement:
--   The source theorem `LevyStochCalc.Driver.product_rule` is extracted from `LevyStochCalc.Driver.ProductRule`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Driver_ProductRule_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The product rule for a continuous Itô process and a pure-jump process

For a continuous version `X` of an Itô process and a bounded adapted process `Y` whose paths are
the sums of finitely many jumps, at the atoms of a Poisson random measure on a window of finite
intensity, the product satisfies

  `X_t Y_t − X_0 Y_0 = ∫_0^t Y_{s−} dX_s + Σ_{atoms (τ, e), τ ≤ t} X_τ ΔY_(τ, e)`

with no covariation term: on the dyadic grids of `[0, t]` the telescoping identity
`Σ Y_{t_k} (X_{t_{k+1}} − X_{t_k}) + Σ X_{t_{k+1}} (Y_{t_{k+1}} − Y_{t_k})` is exact, the first sum
is the Itô integral of the frozen process (`Brownian/LeftFreeze.lean`) plus a Riemann sum of the
drift, and the second converges pathwise to the jump sum (`Analysis/FiniteJumpSum.lean`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Driver

open LevyStochCalc.Analysis LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

section Core

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t)

end Core

section Wrapper

variable [MeasurableSingletonClass E] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] (N : Poisson.PoissonRandomMeasure P ν)

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
  (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Driver.product_rule {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
    (hX : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ} (hB : ∀ ω s, |bdrift ω s| ≤ B)
    {R : Set (ℝ × E)} (hRm : MeasurableSet R)
    (hRfin : Poisson.referenceIntensity ν R ≠ ⊤) {g : Ω → ℝ × E → ℝ}
    (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s))
    (hY : ∀ᵐ ω ∂P, ∀ s,
      Y s ω = Y 0 ω + ∫ p in R ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ, g ω p ∂(N.N ω))
    (Yminus : ℝ → Ω → ℝ) (hYmb : ∀ s ω, |Yminus s ω| ≤ C)
    (hYminus : ∀ᵐ ω ∂P, ∀ s,
      Yminus s ω = Y 0 ω + ∫ p in R ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ, g ω p ∂(N.N ω))
    (hmm' : Measurable (Function.uncurry fun ω s => Yminus s ω * H ω s))
    (hmp' : Probability.ProgressivelyMeasurable ℱ fun ω s => Yminus s ω * H ω s)
    (hmq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, X t ω * Y t ω - X 0 ω * Y 0 ω
      = stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq' t ω
        + (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
        + ∫ p in R ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ, X p.1 ω * g ω p ∂(N.N ω) := by sorry
