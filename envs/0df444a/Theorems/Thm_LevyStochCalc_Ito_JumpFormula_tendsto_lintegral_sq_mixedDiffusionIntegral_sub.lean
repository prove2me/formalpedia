-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_tendsto_lintegral_sq_mixedDiffusionIntegral_sub
-- name    : LevyStochCalc.Ito.JumpFormula.tendsto_lintegral_sq_mixedDiffusionIntegral_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:39:05.379355+00:00
-- url     : https://prove2.me/theorems/5d53498f-065b-4b64-9f38-4f38ddb0c9ab
-- title:
--   tendsto lintegral sq mixedDiffusionIntegral sub
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_lintegral_sq_mixedDiffusionIntegral_sub` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limit steps of the Itô–Lévy formula at bounded derivatives

Along a family of paths converging to the solution of a jump diffusion at almost every time of a
window, the four term families of the Itô–Lévy formula converge to their counterparts along the
solution: the Brownian integrals of the mixed diffusion integrands and the compensated integrals
of the cut mixed jump increments converge in `L²`, and the mixed drift and compensator-drift
integrals converge almost surely. The compensator-drift step rests on a form of dominated
convergence for a mark integral over a shrinking family of cuts in which the domination and the
pointwise convergence are asked at almost every time of the window only.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DominatedAe

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

end DominatedAe

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

open LevyStochCalc.Ito.IntegralLimit in

theorem _root_.LevyStochCalc.Ito.JumpFormula.tendsto_lintegral_sq_mixedDiffusionIntegral_sub (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (hc0 : 0 ≤ c) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (hym : ∀ (k : ℕ) (j : Fin d), Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j))
    (hyp : ∀ (k : ℕ) (j : Fin d), Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
    (hyq : ∀ (k : ℕ) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hσm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
    (hσq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T)
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => y k s ω) atTop (𝓝 (X.X s ω))) (j : Fin d) :
    Tendsto (fun k => ∫⁻ ω,
      (‖stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
          (hym k j) (hyp k j) (hyq k j) T ω
        - stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
          (hσm j) (hσp j) (hσq j) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by sorry
