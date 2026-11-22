-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_tendsto_nhdsLT_sum_filter_le
-- name    : LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T09:39:35.868773+00:00
-- url     : https://prove2.me/theorems/5df137d7-418e-467c-a8b3-72c0caba806d
-- title:
--   tendsto nhdsLT sum filter le
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le` is extracted from `LevyStochCalc.Ito.AtomJumpRelation`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The left-limit jump sum as a step function of the arrival times

Over a window of finite intensity a Poisson random measure is a finite sum of Dirac masses
carried by pairwise distinct times, so the integral of a function against it over an initial
segment of the window is the plain sum of the function's values at the atoms whose time has been
reached. Read at the jump coefficient along the left limits of a path, this writes the
left-limit jump sum over the window as a step function of the arrival times.

## Main statements

* `LevyStochCalc.Poisson.setIntegral_Ioc_prod_eq_sum_filter` — the integral over an initial
  segment of the window is the sum over the atoms whose time has been reached.
* `LevyStochCalc.Poisson.stochasticIntegral_add_setIntegral_sub_eq_pathwise_sub` — the jump side
  of the Itô–Lévy formula at finite activity reads the integrand only at the atoms.
* `LevyStochCalc.Poisson.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero` — an integrand
  vanishing at every atom of the window has compensated integral minus its compensator, on the
  set of sample points where the vanishing holds.
* `LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le` — the left limit of a step
  function with finitely many steps drops the steps at the point itself.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jumpSumLeftAt_eq_sum` — the left-limit
  jump sum over the window is that step function.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma` — the increment of a path
  across an arrival time is the jump coefficient at the left limit there.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

section Restriction

variable {E : Type v} [MeasurableSpace E]

end Restriction

section JumpSide

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end JumpSide

end LevyStochCalc.Poisson

namespace LevyStochCalc.Ito.JumpSplitting

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

theorem _root_.LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le {K : ℕ} (θ : Fin K → ℝ) (c : Fin K → ℝ) (b : ℝ) :
    Tendsto (fun t => ∑ j ∈ Finset.univ.filter fun j => θ j ≤ t, c j)
      (𝓝[<] b) (𝓝 (∑ j ∈ Finset.univ.filter fun j => θ j < b, c j)) := by sorry
