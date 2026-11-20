-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_memLp_brownian
-- name    : LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_brownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:11:17.490595+00:00
-- url     : https://prove2.me/theorems/cf005278-269e-4cec-985f-73af7253b8b7
-- title:
--   simpleIntegral memLp brownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_brownian` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionLp`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L²` lift of the simple-integrand integral

Lifts `simpleIntegral W H T` into `Lp ℝ 2 P` for an adapted `SimplePredictable`
integrand `H`, shows that this lift is Cauchy along an `L²`-dense approximating
sequence of simple predictable integrands, and identifies the squared `L²`-norm of
the resulting limit `itoIntegralLp_brownian` with the time-space integral
`∫⁻ ω, ∫⁻ s in [0, T], ‖H ω s‖₊² ∂volume ∂P`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H T ω) 2 P := by sorry
