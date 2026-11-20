-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_memLp_compensated
-- name    : LevyStochCalc.Poisson.Compensated.simpleIntegral_memLp_compensated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:44:52.199428+00:00
-- url     : https://prove2.me/theorems/61ca66a2-86f2-4df7-9ce2-b21a93654b60
-- title:
--   simpleIntegral memLp compensated
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_memLp_compensated` is extracted from `LevyStochCalc.Poisson.CompensatedIsometryL2`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# L²-isometry of the simple compensated-Poisson integral

Expansion of `(∑_i ξ_i · Ñ(B_i))²` into its diagonal and off-diagonal terms, the resulting
isometry `∫⁻ ‖simpleIntegral N φ T‖² ∂P = ∫⁻ ∫⁻ ∫⁻ ‖φ.eval‖² ∂ν ∂volume ∂P` together with
its Bochner sum form `∑_i ν̂(fullRect i).toReal · ∫ ξ_i² ∂P`, the finiteness of the
`L²`-norm and the membership `MemLp (simpleIntegral N φ T) 2 P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ## Square integrability of the simple compensated integral

The simple integral `simpleIntegral N φ T` of an adapted simple integrand has finite second
moment and lies in `L²(P)`; the Brownian counterpart is the lift
`LevyStochCalc.Brownian.Ito.simpleIntegralLp_brownian` to `Lp ℝ 2 P`. -/

theorem _root_.LevyStochCalc.Poisson.Compensated.simpleIntegral_memLp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral N φ T ω) 2 P := by sorry
