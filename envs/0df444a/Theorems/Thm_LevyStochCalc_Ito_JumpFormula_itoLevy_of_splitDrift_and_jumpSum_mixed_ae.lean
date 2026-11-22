-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_itoLevy_of_splitDrift_and_jumpSum_mixed_ae
-- name    : LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T09:41:27.757759+00:00
-- url     : https://prove2.me/theorems/4b3c7b50-7d46-45ef-97cb-267ce37060c5
-- title:
--   itoLevy of splitDrift and jumpSum mixed ae
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_ae` is extracted from `LevyStochCalc.Ito.FiniteActivityMixedPrelims`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Preliminaries for the finite-activity Itô–Lévy identity in the mixed form

The small facts the finite-activity identity along a truncated path assembles from: the
left-limit jump sum of the mark-cut coefficient bundle is the prescribed-path jump sum along the
left limits; the left limit of the time-augmented path; the value of a progressively measurable
vector process at a stopping time is known at that time; the drift reconciliation for the mixed
integrands asked at almost every time only; and the bounds on the partial derivatives of the
time-augmented representative of a state function with bounded derivatives.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath`
* `LevyStochCalc.Ito.JumpFormula.leftLim_timeAugProcess_eq_cons`
* `LevyStochCalc.Ito.JumpFormula.measurable_stoppingTime_eval_untopA`
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_ae`
* `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv_timeAug_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv₂_timeAug_mul_le`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Probability LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section JumpSum

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

end JumpSum

section LeftLimit

variable {Ω : Type u} {n : ℕ}

end LeftLimit

section StoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}

end StoppingTime

section MixedAe

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end MixedAe

section MixedAssemblyAe

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : JumpDiffusionCoeffs n d E}

theorem _root_.LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_ae {A : Set E} {y x : ℝ → Fin n → ℝ} {T : ℝ}
    {Dm Cm Js : ℝ}
    (hγ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn
      (fun s => ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s) (x s))
      (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν) :
    u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν := by sorry
