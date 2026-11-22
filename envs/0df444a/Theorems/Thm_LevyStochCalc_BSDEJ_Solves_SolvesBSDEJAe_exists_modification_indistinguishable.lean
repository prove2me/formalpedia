-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_SolvesBSDEJAe_exists_modification_indistinguishable
-- name    : LevyStochCalc.BSDEJ.Solves.SolvesBSDEJAe.exists_modification_indistinguishable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:50:12.068207+00:00
-- url     : https://prove2.me/theorems/37b80dea-4ba5-4729-bd3d-a4d0756dd0af
-- title:
--   exists modification indistinguishable
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJAe.exists_modification_indistinguishable` is extracted from `LevyStochCalc.BSDEJ.SolvesAe`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SolvesAe_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of a BSDEJ up to a null set of sample points

`SolvesBSDEJAe D f ξ T Y Z U` is the solution predicate `SolvesBSDEJ D f ξ T Y Z U` with its
three everywhere-quantified path conditions — right-continuity with left limits of `Y`, and the
vanishing of `Z` and of `U` off the horizon — asked only for almost every sample point.

The two predicates describe the same solutions: setting the three processes to `0` on a
measurable null superset of the exceptional set produces a `SolvesBSDEJ` triple whose paths agree
with the given ones off that null set (`SolvesBSDEJAe.exists_modification`), so the value
processes of two almost-everywhere solutions of the same equation remain indistinguishable on the
horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

open LevyStochCalc.Brownian.Multidim LevyStochCalc.Poisson in

theorem _root_.LevyStochCalc.BSDEJ.Solves.SolvesBSDEJAe.exists_modification_indistinguishable
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJAe D f ξ T Y Z U) :
    ∃ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y' Z' U' ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, Y' t ω = Y t ω)
        ∧ (∀ᵐ ω ∂P, ∀ s : ℝ, Z' s ω = Z s ω) ∧ ∀ᵐ ω ∂P, ∀ s : ℝ, U' s ω = U s ω := by sorry
