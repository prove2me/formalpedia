-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_isTightMeasureSet_of_totallyBounded
-- name    : LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T23:28:50.113286+00:00
-- url     : https://prove2.me/theorems/b21d53e3-e57f-4895-bb65-93a9ac6b098e
-- title:
--   isTightMeasureSet of totallyBounded
-- statement:
--   The source theorem `LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded` is extracted from `LevyStochCalc.Probability.LevyProkhorovComplete`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the Lévy–Prokhorov metric

On a proper metric space `Ω` (for instance `ℝ` or `ℝⁿ`) with its Borel σ-algebra, the
Lévy–Prokhorov metric on probability measures is complete.

A totally bounded set of probability measures is tight: take a finite `ε/2`-net, a compact set `K`
carrying all but `ε/2` of the mass of each net point, and the closed `ε/2`-thickening of `K`, which
is compact because `Ω` is proper; the Lévy–Prokhorov thickening inequality transfers the mass bound
from each net point to every measure near it. By Prokhorov's theorem a tight set has compact
closure, so the range of a Cauchy sequence is relatively compact and the sequence converges.

## Main statements

* `LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded` — a totally bounded set of
  probability measures is tight.
* `LevyStochCalc.Probability.isCompact_closure_of_isTightMeasureSet_levyProkhorov` — Prokhorov's
  theorem in the Lévy–Prokhorov metric: a tight set has compact closure.
* `LevyStochCalc.Probability.instCompleteSpaceLevyProkhorovProbabilityMeasure` — the
  Lévy–Prokhorov metric space of probability measures is complete.
-/

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MetricSpace Ω] [ProperSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

theorem _root_.LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded
    (S : Set (LevyProkhorov (ProbabilityMeasure Ω))) (hS : TotallyBounded S) :
    IsTightMeasureSet {(μ.toMeasure.toMeasure : Measure Ω) | μ ∈ S} := by sorry
