-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_measurableSet_predictableSigma_Ioc_prod
-- name    : LevyStochCalc.Probability.measurableSet_predictableSigma_Ioc_prod
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:01:43.571179+00:00
-- url     : https://prove2.me/theorems/33e19fcc-8047-4185-b7e6-d45bd061c9d4
-- title:
--   measurableSet predictableSigma Ioc prod
-- statement:
--   The source theorem `LevyStochCalc.Probability.measurableSet_predictableSigma_Ioc_prod` is extracted from `LevyStochCalc.Probability.PredictableModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_PredictableModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of progressive integrands

The elementary integrands of the `L²` theory — finite sums of a coefficient measurable at the
left endpoint of a cell, carried on that cell — are predictable, and the predictable processes
are closed under pointwise upper limits. Since the elementary integrands are dense in the
progressive integrands of finite energy, a progressive integrand agrees with a predictable one
almost everywhere in time and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Cells

theorem _root_.LevyStochCalc.Probability.measurableSet_predictableSigma_Ioc_prod {r q : ℝ} (hrq : r ≤ q) {A : Set Ω}
    (hA : MeasurableSet[ℱ r] A) :
    MeasurableSet[predictableSigma ℱ] (Set.Ioc r q ×ˢ A) := by sorry
