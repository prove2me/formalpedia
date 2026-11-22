-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_ae_forall_jumpSumAt_eq_cappedJumpSumAt
-- name    : LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSumAt_eq_cappedJumpSumAt
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:47:06.671153+00:00
-- url     : https://prove2.me/theorems/ee88403e-1207-406f-9468-2df3eff9eaf0
-- title:
--   ae forall jumpSumAt eq cappedJumpSumAt
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSumAt_eq_cappedJumpSumAt` is extracted from `LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The capped jump chain over a prescribed evaluation path

The pathwise sum of the jumps carried by a mark set over a window reads the jump coefficient at a
prescribed path of states, and capping the arrival times at the horizon turns that sum into the
chain of jumps accumulated up to each arrival time. Over an enumeration of the atoms of the
window the jump sum is the sum of the jump coefficient over the enumerated atoms whose times lie
in the sub-window, so the capped sum gains exactly the jump coefficient carried by each arrival
time inside the window and does not move strictly between consecutive arrival times; a path that
splits at all nonnegative times into a continuous part and that jump sum is therefore the
continuous part translated by the capped jump sum on each such interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Defs

end Defs

section GeneralShift

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (A : Set E)

end GeneralShift

section MarkIdentification

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

end MarkIdentification

section CappedChain

variable {A : Set E}

theorem _root_.LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSumAt_eq_cappedJumpSumAt
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      ∀ i : Fin n, jumpSumAt X Y A s ω i = cappedJumpSumAt X Y A T k ω i := by sorry
