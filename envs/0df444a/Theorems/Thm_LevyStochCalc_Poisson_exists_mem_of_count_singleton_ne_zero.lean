-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_exists_mem_of_count_singleton_ne_zero
-- name    : LevyStochCalc.Poisson.exists_mem_of_count_singleton_ne_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:26:11.391358+00:00
-- url     : https://prove2.me/theorems/cd6599db-71d7-4eee-b9cd-cd8c348e759b
-- title:
--   exists mem of count singleton ne zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.exists_mem_of_count_singleton_ne_zero` is extracted from `LevyStochCalc.Poisson.JumpTimesEnum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times as the atom times of a Poisson random measure

The counting process `arrivalCount N A` splits at a positive time into the mass strictly before
that time and the mass carried by the time itself, so on a window on which the restricted measure
is integer-valued a time in `(0, T]` carries mass in the mark set `A` exactly when it is one of
the arrival times `jumpTime N A i`. Such a time therefore lies among the times of any finite atom
set of the restricted measure. Every arrival time of positive index is strictly positive, the
arrival times of a time-simple measure strictly increase, and the chain of arrival times passes
any horizon at which the count is finite.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Singleton

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Singleton

section IntegerValued

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end IntegerValued

section Positivity

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Positivity

section AtomTimes

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomTimes

section Chain

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Chain

section AtomFinset

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

theorem _root_.LevyStochCalc.Poisson.exists_mem_of_count_singleton_ne_zero (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    {s : Finset (ℝ × E)}
    (hs : ∀ g : ℝ × E → ℝ≥0∞,
      ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
        = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} * g p)
    {u : ℝ} (hu0 : 0 < u) (huT : u ≤ T) (hne : N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0) :
    ∃ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0 ∧ p.1 = u := by sorry
