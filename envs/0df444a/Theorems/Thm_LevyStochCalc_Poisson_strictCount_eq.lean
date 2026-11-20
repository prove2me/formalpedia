-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_strictCount_eq
-- name    : LevyStochCalc.Poisson.strictCount_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:57:40.006821+00:00
-- url     : https://prove2.me/theorems/afa49e86-ebae-4d44-9789-dc4b7db227c6
-- title:
--   strictCount eq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.strictCount_eq` is extracted from `LevyStochCalc.Poisson.StrictCount`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_StrictCount_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strictly-past count of a Poisson random measure is predictable

The left endpoint of the level-`n` dyadic slab containing a positive time increases to that time
from strictly below, so the count of a set strictly before the time is the supremum over the
levels of the counts up to those endpoints. Each of those is a step process constant on the slabs
with a coefficient known at the left endpoint, hence predictable, and a countable supremum in the
extended nonnegative reals is measurable: the strictly-past count is predictable for every sample
point, with no null set involved.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Dyadic

end Dyadic

section Count

variable (N : PoissonRandomMeasure P ν)

theorem _root_.LevyStochCalc.Poisson.strictCount_eq {C : Set (ℝ × E)} {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) (ω : Ω) :
    strictCount N C A T ω s e = N.N ω (C ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ) := by sorry
