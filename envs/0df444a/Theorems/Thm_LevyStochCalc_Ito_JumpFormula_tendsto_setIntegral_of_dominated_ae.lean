-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_tendsto_setIntegral_of_dominated_ae
-- name    : LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T12:43:50.033358+00:00
-- url     : https://prove2.me/theorems/f1eb0701-9787-4a51-86ca-72a80d59a5b2
-- title:
--   tendsto setIntegral of dominated ae
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated_ae` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated_ae
    {T : ℝ} {A : ℕ → Set E} {fs : ℕ → ℝ → E → ℝ} {f g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable (fun p : ℝ × E => fs m p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e, |fs m s e| ≤ g s e)
    (hconv : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e,
      Tendsto (fun m => fs m s e) atTop (𝓝 (f s e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν)) := by sorry
