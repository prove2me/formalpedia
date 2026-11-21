-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_pairing_joint_value_characterMultidim_eq_zero
-- name    : LevyStochCalc.Driver.pairing_joint_value_characterMultidim_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:02:43.028947+00:00
-- url     : https://prove2.me/theorems/dec77ed1-74ea-4182-83ec-e8137f45b6d9
-- title:
--   pairing joint value characterMultidim eq zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.pairing_joint_value_characterMultidim_eq_zero` is extracted from `LevyStochCalc.Driver.JointMultidim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointMultidim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mixed cell lemma for a multidimensional Brownian motion

A character of a vector of Brownian increments across a cell is the character of the increment
of a unit combination, scaled by the length of the weight vector, so the mixed cell lemma for a
single Brownian motion carries over to the multidimensional driver with the Poisson character
riding along unchanged.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Cell

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

end Cell

section Grid

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

theorem _root_.LevyStochCalc.Driver.pairing_joint_value_characterMultidim_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) (hTn : τ n < T) :
    ∫ ω, ((Z ω : ℝ) : ℂ)
        * (Complex.exp (Complex.I * ((∑ i, ∑ k ∈ Finset.Ico 1 (n + 1),
            c k i * (W.W i).W (τ k) ω : ℝ) : ℂ))
          * charAt N w Bfam (τ n) ω) ∂P = 0 := by sorry
