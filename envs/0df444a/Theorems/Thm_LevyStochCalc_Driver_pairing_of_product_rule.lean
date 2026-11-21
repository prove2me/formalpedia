-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_pairing_of_product_rule
-- name    : LevyStochCalc.Driver.pairing_of_product_rule
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:00:30.483563+00:00
-- url     : https://prove2.me/theorems/fa5e8b86-2bb5-40be-873f-ce8b014005b0
-- title:
--   pairing of product rule
-- statement:
--   The source theorem `LevyStochCalc.Driver.pairing_of_product_rule` is extracted from `LevyStochCalc.Driver.CellPairing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellPairing_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing the jump term of the product rule

A weight orthogonal to every compensated integral over the horizon does not see the compensated
half of a window integral against the random measure: pairing it, times a bounded weight
measurable before the window, with the integral of a continuous adapted factor against the
random measure leaves only the integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section JumpTerm

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ}

end JumpTerm

section BrownianTerm

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end BrownianTerm

section Assembly

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

include hℱN hℱW in

theorem _root_.LevyStochCalc.Driver.pairing_of_product_rule {T : ℝ} (hT : 0 < T) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (haT : a ≤ T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {Xg : ℝ → Ω → ℝ} (hXc : ∀ ω, Continuous fun t => Xg t ω)
    (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (Xg t)) {C : ℝ} (hC0 : 0 ≤ C)
    (hXb : ∀ s ω, |Xg s ω| ≤ C)
    {Y Yminus : ℝ → Ω → ℝ} (hYm : ∀ s, Measurable (Y s)) (hYb : ∀ s ω, |Y s ω| ≤ 1)
    (hYmm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Yminus s ω))
    (hYmb : ∀ s ω, |Yminus s ω| ≤ 1)
    {bdrift : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ}
    (hBb : ∀ ω s, |bdrift ω s| ≤ B)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ}
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hid : ∀ᵐ ω ∂P, Xg t ω * Y t ω - Xg 0 ω * Y 0 ω
      = stochasticIntegralBrownian W ℱ hℱW
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω
        + (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) :
    ∫ ω, Z ω * V ω * (Xg t ω * Y t ω) ∂P
      = ∫ ω, Z ω * V ω * (Xg 0 ω * Y 0 ω) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            Yminus s ω * bdrift ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            Xg q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by sorry
