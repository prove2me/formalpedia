-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_progressivelyMeasurable_mul_indIoc
-- name    : LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T18:57:53.990437+00:00
-- url     : https://prove2.me/theorems/74ce991f-9573-4fea-af59-46191d6afdf8
-- title:
--   progressivelyMeasurable mul indIoc
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc` is extracted from `LevyStochCalc.Brownian.ItoPullOut`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside an Itô integral over a window

A bounded `ℱ_a`-measurable weight times the Itô integral of an integrand supported in `(a, b]` is
the Itô integral of the weighted integrand: the weight times the indicator is itself a simple
integrand, so this is associativity against a simple integrand.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M)
    (hVm : Measurable V) (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s := by sorry
