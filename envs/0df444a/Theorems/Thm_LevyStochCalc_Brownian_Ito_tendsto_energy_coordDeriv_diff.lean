-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_coordDeriv_diff
-- name    : LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:51:10.543983+00:00
-- url     : https://prove2.me/theorems/6833cac8-d6fe-4030-9be0-4bdc7d27fa98
-- title:
--   tendsto energy coordDeriv diff
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff` is extracted from `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002

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

theorem _root_.LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by sorry
