-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_aestronglyMeasurable_iInf_of_antitone
-- name    : LevyStochCalc.Probability.aestronglyMeasurable_iInf_of_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:33:10.371303+00:00
-- url     : https://prove2.me/theorems/c57e3c61-183f-46c3-9e5d-47321f997f0f
-- title:
--   aestronglyMeasurable iInf of antitone
-- statement:
--   The source theorem `LevyStochCalc.Probability.aestronglyMeasurable_iInf_of_antitone` is extracted from `LevyStochCalc.Probability.AEMeasurableInf`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A.e. measurability for the infimum of a decreasing sequence of σ-algebras

A real function a.e.-measurable for every member of an antitone sequence of sub-σ-algebras is
a.e.-measurable for their infimum. The witness is the `limsup` of the approximants: dropping the
first `N` terms does not change a `limsup`, and after that every approximant is `m N`-measurable,
while on the a.e. set where all the approximants agree with `f` the `limsup` is `f` itself.

This is the step that identifies `⨅ n, lpMeas (m n)` with `lpMeas (⨅ n, m n)`, which is what turns
the convergence of orthogonal projections (`LevyStochCalc/Probability/ProjectionLimit.lean`) into
convergence of conditional expectations along a decreasing filtration.
-/

open MeasureTheory Filter
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem _root_.LevyStochCalc.Probability.aestronglyMeasurable_iInf_of_antitone {m : ℕ → MeasurableSpace Ω} (hanti : Antitone m)
    {f : Ω → ℝ} (hf : ∀ n, AEStronglyMeasurable[m n] f μ) :
    AEStronglyMeasurable[⨅ n, m n] f μ := by sorry
