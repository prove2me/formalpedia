-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_sq_lintegral_eq
-- name    : LevyStochCalc.Brownian.Ito.simpleIntegral_sq_lintegral_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:29:40.361668+00:00
-- url     : https://prove2.me/theorems/25b3445a-6cd1-4698-8691-95f8cdb5f3b5
-- title:
--   simpleIntegral sq lintegral eq
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_sq_lintegral_eq` is extracted from `LevyStochCalc.Brownian.ItoSimpleIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô isometry on simple predictable integrands

Expanding the square of the elementary integral into its diagonal and off-diagonal terms gives,
for an adapted simple predictable integrand `H` and a scalar Brownian motion `W`,
`E[(∫_0^T H dW) ^ 2] = ∑_i (t_{i+1} - t_i) · E[ξ_i ^ 2]`; combined with the energy of the
integrand this is the L²-isometry `E[(∫_0^T H dW) ^ 2] = ∫_0^T E[(H.eval s) ^ 2] ds`, stated
both for the lower integral and for the Bochner integral.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.LevyStochCalc.Brownian.Ito.simpleIntegral_sq_lintegral_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by sorry
