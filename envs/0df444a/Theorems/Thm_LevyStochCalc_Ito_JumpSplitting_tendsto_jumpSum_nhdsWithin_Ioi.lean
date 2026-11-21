-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_tendsto_jumpSum_nhdsWithin_Ioi
-- name    : LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:44:41.282914+00:00
-- url     : https://prove2.me/theorems/64fc360e-8f8e-4178-8dc9-1a6e8a9a6268
-- title:
--   tendsto jumpSum nhdsWithin Ioi
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi` is extracted from `LevyStochCalc.Ito.JumpSplittingAllTimes`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity splitting at all nonnegative times

The finite-activity splitting of a jump diffusion is an identity between the path, a vector Itô
process and a pathwise jump sum, valid almost surely at each fixed nonnegative time. The jump sum
over `(0, t]` is right-continuous in `t` on a window carrying an integrable jump coefficient and a
jump diffusion has almost surely càdlàg paths, so the identity extends from the nonnegative
rationals to all of `[0, ∞)` on a single set of full measure, for any modification of the vector
Itô process whose paths are right-continuous.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi` — right-continuity in time of
  the pathwise jump sum.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat` — two almost surely right-continuous
  processes agreeing almost surely at each nonnegative rational time agree almost surely at every
  nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSum` — the finite-activity splitting,
  almost surely at all nonnegative times simultaneously.
* `LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_of_measure_zero` — the jump sum is constant across a
  window carrying no mass of the random measure.
* `LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall` — the splitting written as a path
  translated by a shift held fixed strictly between consecutive members of a chain of times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Rationals

end Rationals

section Upgrade

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Upgrade

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {i : Fin n}
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) {ω : Ω}
    (hint : ∀ T : ℝ, IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)) (t : ℝ) :
    Filter.Tendsto (fun s => jumpSum X A s ω i) (nhdsWithin t (Set.Ioi t))
      (nhds (jumpSum X A t ω i)) := by sorry
