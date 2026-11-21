-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_tendsto_quadVar_clamp
-- name    : LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:48:56.639342+00:00
-- url     : https://prove2.me/theorems/53533982-6cb6-4da4-9e42-6802401076b7
-- title:
--   ae tendsto quadVar clamp
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp` is extracted from `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hf''c : Continuous f'')
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (Y i s ω)
          * ∑ k : Fin d, clampCoeff H (ns i) p k ω s * clampCoeff H (ns i) q k ω s ∂volume)
      Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) := by sorry
