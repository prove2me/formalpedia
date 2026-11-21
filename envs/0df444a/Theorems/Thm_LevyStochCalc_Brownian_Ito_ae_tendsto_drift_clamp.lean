-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_tendsto_drift_clamp
-- name    : LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:52:20.673303+00:00
-- url     : https://prove2.me/theorems/f324d153-e4ba-4e73-a424-7cef76b5f4ab
-- title:
--   ae tendsto drift clamp
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp` is extracted from `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands of the clamped approximation of a vector Itô process

For a function whose first and second derivatives are bounded, the drift integrals, the quadratic
variation terms and the diffusion integrands built from the coefficients clamped at a level growing
to infinity converge to the ones built from the original coefficients: the drift and quadratic
variation terms pathwise, the diffusion integrands in energy on a bounded window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {T : ℝ}
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (Y i s ω) * clampDrift b (ns i) p ω s ∂volume) Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * b p ω s ∂volume)) := by sorry
