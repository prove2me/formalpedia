-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_ae_forall_eq_of_ae_rat
-- name    : LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:44:44.438087+00:00
-- url     : https://prove2.me/theorems/eca2713e-f8d4-4818-8eb3-93bd314fb538
-- title:
--   ae forall eq of ae rat
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat` is extracted from `LevyStochCalc.Ito.JumpSplittingAllTimes`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F000

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

theorem _root_.LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat {Y Z : ℝ → Ω → ℝ}
    (hrat : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ᵐ ω ∂P, Y (q : ℝ) ω = Z (q : ℝ) ω)
    (hY : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)))
    (hZ : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Z t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω = Z t ω := by sorry
