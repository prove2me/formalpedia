-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_predictable_pointwise_tendsto_per_omega
-- name    : LevyStochCalc.Brownian.Ito.predictable_pointwise_tendsto_per_omega
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T10:14:04.465178+00:00
-- url     : https://prove2.me/theorems/bda06b5d-cfdb-4606-acc7-6a41b7ac3afc
-- title:
--   predictable pointwise tendsto per omega
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.predictable_pointwise_tendsto_per_omega` is extracted from `LevyStochCalc.Brownian.ItoDensityPointwise`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-everywhere convergence of the dyadic averages

Lebesgue differentiation for a bounded jointly measurable integrand: the dyadic cell
averages, shifted and unshifted, converge to the integrand at almost every point of
`Ω × [0,T]`, and for the unshifted family the convergence also holds in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.predictable_pointwise_tendsto_per_omega
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by sorry
