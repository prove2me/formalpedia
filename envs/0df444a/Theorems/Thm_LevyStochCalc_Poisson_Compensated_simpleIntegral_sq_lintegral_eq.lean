-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_sq_lintegral_eq
-- name    : LevyStochCalc.Poisson.Compensated.simpleIntegral_sq_lintegral_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:49:33.312773+00:00
-- url     : https://prove2.me/theorems/d07f5964-232c-447b-8068-3e5e45523bcc
-- title:
--   simpleIntegral sq lintegral eq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_sq_lintegral_eq` is extracted from `LevyStochCalc.Poisson.CompensatedIsometryL2`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F000

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

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.LevyStochCalc.Poisson.Compensated.simpleIntegral_sq_lintegral_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (_hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) *
        ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by sorry
