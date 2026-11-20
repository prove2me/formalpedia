-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_sub_sq_weighted
-- name    : LevyStochCalc.Poisson.Compensated.simpleIntegral_sub_sq_weighted
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T17:08:20.332343+00:00
-- url     : https://prove2.me/theorems/5c1e6f17-77b7-4cff-b390-1e82cebf40c6
-- title:
--   simpleIntegral sub sq weighted
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_sub_sq_weighted` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleQuadratic`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Quadratic-variation martingale of the compensated simple integral

The set-level weighted isometry `∫ g·(Iₜ − Iₛ)² = ∑_i ν̂(Rᵢ).toReal · ∫ g·ξᵢ²` over the
increment boxes `Rᵢ = timeRect i t \ timeRect i s`, membership of `simpleIntegral N φ t` in
`L²(P)` at every running time, its vanishing at nonpositive times, and the resulting
martingale property of the compensated square
`t ↦ (simpleIntegral N φ t)² − ∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` with respect to a Poisson
filtration; also the joint measurability of the simple integrand `eval` in `(s, e, ω)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.simpleIntegral_sub_sq_weighted
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ s) g)
    {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
    ∫ ω, g ω * (simpleIntegral N φ t ω - simpleIntegral N φ s ω) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν
            (φ.timeRect i t \ φ.timeRect i s)).toReal
          * ∫ ω, g ω * (φ.ξ i ω) ^ 2 ∂P := by sorry
