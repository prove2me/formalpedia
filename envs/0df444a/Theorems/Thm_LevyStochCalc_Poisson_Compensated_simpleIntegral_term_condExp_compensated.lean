-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_term_condExp_compensated
-- name    : LevyStochCalc.Poisson.Compensated.simpleIntegral_term_condExp_compensated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:59:28.419276+00:00
-- url     : https://prove2.me/theorems/0570db57-ac09-40dc-8c29-d853a7b4a077
-- title:
--   simpleIntegral term condExp compensated
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_term_condExp_compensated` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleAdapted`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to a Poisson filtration `ℱ` of `N`: each time-rectangle
`timeRect i t` lies in the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable,
and the coefficient `ξᵢ` is `ℱ_t`-measurable once `t` reaches the partition point (the term
vanishing before). Each summand is `P`-integrable, its conditional expectation satisfies
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` for `0 ≤ s ≤ t`, and summing over the
partition gives the martingale property of `t ↦ simpleIntegral N φ t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

set_option maxHeartbeats 1000000 in
-- The Case-B tower-property chain (`condExp_mul` + `condExp_condExp_of_le`) is
-- heartbeat-heavy; raise the budget for this single proof.

theorem _root_.LevyStochCalc.Poisson.Compensated.simpleIntegral_term_condExp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω
        | ℱ s]
      =ᵐ[P] fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω := by sorry
