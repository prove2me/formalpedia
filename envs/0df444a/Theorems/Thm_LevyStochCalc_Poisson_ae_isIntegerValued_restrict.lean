-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_isIntegerValued_restrict
-- name    : LevyStochCalc.Poisson.ae_isIntegerValued_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:26:56.561405+00:00
-- url     : https://prove2.me/theorems/84711406-69f9-4c80-a139-e1ca6622c5e3
-- title:
--   ae isIntegerValued restrict
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_isIntegerValued_restrict` is extracted from `LevyStochCalc.Poisson.Atomic`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Atomicity of a Poisson random measure on a finite-activity window

A Poisson random measure carries a natural mass on each measurable set of finite intensity, one
set at a time and only almost surely. Over a window of finite intensity the counts on a countable
generating π-system are simultaneously natural on a single event of full measure, and the sets of
natural mass form a Dynkin system, so on that event the restricted measure is integer-valued. On
a countably separated mark space it is then a finite sum of Dirac masses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section CountablyGenerated

variable [MeasurableSpace.CountablyGenerated E]

theorem _root_.LevyStochCalc.Poisson.ae_isIntegerValued_restrict (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, Probability.IsIntegerValued ((N.N ω).restrict R) := by sorry
