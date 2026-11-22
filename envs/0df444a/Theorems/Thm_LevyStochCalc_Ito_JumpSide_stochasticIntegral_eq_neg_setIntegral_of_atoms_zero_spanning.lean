-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSide_stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning
-- name    : LevyStochCalc.Ito.JumpSide.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T09:47:55.787911+00:00
-- url     : https://prove2.me/theorems/b882900f-3086-49d3-aeaf-13f465c7109b
-- title:
--   stochasticIntegral eq neg setIntegral of atoms zero spanning
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSide.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning` is extracted from `LevyStochCalc.Ito.JumpSideCompensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSideCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A predictable integrand vanishing at the atoms

On a window of finite intensity the compensated integral of a predictable integrand is the
integral against the random measure minus the integral against the reference intensity, so an
integrand vanishing at every atom of the window has compensated integral minus its compensator.
The mark sets of finite intensity exhaust the mark space, the compensated integrals of the cut
integrands converge to the compensated integral of the integrand, and the compensators converge
to the compensator, so the identity survives at infinite activity.

## Main statements

* `stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning` — the identity for an integrand
  vanishing at the atoms of every window built from the spanning sets of the mark measure. Both
  the vanishing and the integrability of the compensator are asked only on a set of sample
  points, and the conclusion holds there: an integrand that is square integrable against the
  intensity need not be integrable against it, so the compensator converges only where the
  hypothesis puts it.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSide

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated LevyStochCalc.Ito.IntegralLimit

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Ito.JumpSide.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hφpred : Probability.MarkedPredictable ℱ ν φ)
    (hφ0 : ∀ (ω : Ω) (s : ℝ) (e : E), s ≤ 0 → φ ω s e = 0) {T : ℝ} (hT : 0 < T) (G : Set Ω)
    (hint : ∀ᵐ ω ∂P, ω ∈ G → IntegrableOn (fun q : ℝ × E => φ ω q.1 q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hatoms : ∀ᵐ ω ∂P, ω ∈ G → ∀ j : ℕ,
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, φ ω q.1 q.2 ∂(N.N ω) = 0) :
    ∀ᵐ ω ∂P, ω ∈ G →
      Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω
        = -∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), φ ω q.1 q.2
            ∂(referenceIntensity ν) := by sorry
