-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_stochasticIntegral_congr_ae
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:37:46.252176+00:00
-- url     : https://prove2.me/theorems/4e2b8642-f7bb-4952-a5cb-b78f39d40fdb
-- title:
--   stochasticIntegral congr ae
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae` is extracted from `LevyStochCalc.Brownian.MultidimItoCongr`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MultidimIto_F000
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The multidimensional Itô integral depends only on the class of its integrand

The multidimensional Itô integral is the sum over the coordinates of the one-dimensional
integrals against the coordinate Brownian motions, and each of those depends only on the
almost-everywhere class of its integrand on the window. Two vector integrands agreeing for almost
every time of a window, at almost every sample point, therefore have almost surely equal
multidimensional integrals at the end of that window.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ)
  {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae
    (hm₁ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω i))
    (hp₁ : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω i)
    (hq₁ : ∀ i : Fin d, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω i))
    (hp₂ : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω i)
    (hq₂ : ∀ i : Fin d, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T), Z₁ s ω = Z₂ s ω) :
    stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂ T := by sorry
