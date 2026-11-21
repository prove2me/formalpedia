-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_pairing_cell_joint_eq_zero
-- name    : LevyStochCalc.Driver.pairing_cell_joint_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:37:42.376025+00:00
-- url     : https://prove2.me/theorems/f50683b6-cf0b-4cf7-94b2-e568d0409f98
-- title:
--   pairing cell joint eq zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.pairing_cell_joint_eq_zero` is extracted from `LevyStochCalc.Driver.CellComplex`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellComplex_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell lemma for a complex bounded factor

The grid induction carries the joint character of the earlier cells as the bounded factor, and
that character is complex. Since the weight stays real, the pairing splits into the real and
imaginary parts of the factor, and the vanishing of the mean against the complex factor is the
vanishing of both real means.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Complex

variable (N : PoissonRandomMeasure P ν)

variable {Z : Ω → ℝ} {V : Ω → ℂ} {Mv l : ℝ} {X : ℝ → Ω → ℝ}

end Complex

section Cell

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

include hℱN hℱW in

theorem _root_.LevyStochCalc.Driver.pairing_cell_joint_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℂ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) (hZV : ∫ ω, ((Z ω : ℝ) : ℂ) * V ω ∂P = 0) :
    ∫ ω, ((Z ω : ℝ) : ℂ) * V ω
      * (Complex.exp (Complex.I * ((l * (W.W b ω - W.W a ω) : ℝ) : ℂ))
        * charAt N w Bfam b ω) ∂P = 0 := by sorry
