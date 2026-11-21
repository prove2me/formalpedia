-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_factor_increment_sq
-- name    : LevyStochCalc.Brownian.Ito.integral_factor_increment_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:38:56.955374+00:00
-- url     : https://prove2.me/theorems/70ac335d-96e3-496b-9656-879136f3dc23
-- title:
--   integral factor increment sq
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_factor_increment_sq` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionConvergence`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.integral_factor_increment_sq
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
      (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * (b - a) := by sorry
