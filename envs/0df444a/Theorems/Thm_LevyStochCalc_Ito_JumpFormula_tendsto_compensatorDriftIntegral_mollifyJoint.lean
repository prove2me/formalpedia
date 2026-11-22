-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_tendsto_compensatorDriftIntegral_mollifyJoint
-- name    : LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegral_mollifyJoint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:52:03.843386+00:00
-- url     : https://prove2.me/theorems/b5b19019-5000-4b78-93ec-a21ca510be0d
-- title:
--   tendsto compensatorDriftIntegral mollifyJoint
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegral_mollifyJoint` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsC12Limits`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12MollifyJoint_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy integrands along a joint mollification

For a `C^{1,2}` function `u` of time and state and a family of bumps on `ℝ × (Fin n → ℝ)` whose
outer radii tend to `0`, the drift, diffusion, jump and compensator-drift integrands of the joint
mollifications of `u` converge pointwise to those of `u`, the time derivative, the gradient and
the Hessian of the mollification converging to their counterparts for `u`. When the derivatives
of `u` are bounded, the same bounds hold for every mollification, so along a jump diffusion the
drift integral over a window and the compensator-drift integral over a window and the mark space
converge almost surely, by dominated convergence against a bound built from the coefficients of
the equation alone.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.tendsto_diffusionIntegrand_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_sub_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegrand_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegrand_mollifyJoint` — pointwise
  convergence of the four integrands of the Itô–Lévy formula along the mollifications.
* `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegral_mollifyJoint` — almost-sure convergence of
  the drift integral along the path of a jump diffusion.
* `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegral_mollifyJoint` — almost-sure
  convergence of the compensator-drift integral along the path of a jump diffusion.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Pointwise

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {u : ℝ → (Fin n → ℝ) → ℝ} {ι : Type*}
  {l : Filter ι} {φ : ι → ContDiffBump (0 : ℝ × (Fin n → ℝ))}

end Pointwise

section Integrals

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegral_mollifyJoint (S : SdeData X) (hu : IsC12 u) {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (T : ℝ) (hT : 0 < T)
    (φ : ℕ → ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand (mollifyJoint u (φ k)) coeffs.γ s (X.X s ω) e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)) := by sorry
