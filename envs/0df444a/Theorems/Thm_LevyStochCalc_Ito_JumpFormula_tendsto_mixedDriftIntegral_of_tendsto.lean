-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_tendsto_mixedDriftIntegral_of_tendsto
-- name    : LevyStochCalc.Ito.JumpFormula.tendsto_mixedDriftIntegral_of_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:41:14.038055+00:00
-- url     : https://prove2.me/theorems/ced546b9-0abf-4bcc-9e3d-a454371afbe9
-- title:
--   tendsto mixedDriftIntegral of tendsto
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_mixedDriftIntegral_of_tendsto` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Ito.JumpFormula.tendsto_mixedDriftIntegral_of_tendsto (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c₀ c₁ c₂ : ℝ}
    (hc₀ : ∀ s x, |timeDeriv u s x| ≤ c₀) (hc₁ : ∀ s x i, |gradient u s x i| ≤ c₁)
    (hc₂ : ∀ s x i j, |hessian u s x i j| ≤ c₂) (hc₂0 : 0 ≤ c₂)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (hym : ∀ i, Measurable (Function.uncurry (y i)))
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun i => y i s ω) atTop (𝓝 (X.X s ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun i => ∫ s in Set.Icc (0 : ℝ) T,
        mixedDriftIntegrand u coeffs s (y i s ω) (X.X s ω)) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))) := by sorry
