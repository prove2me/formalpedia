-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_cappedJumpSumAt_succ_eq_add_gamma
-- name    : LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_add_gamma
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:50:52.690356+00:00
-- url     : https://prove2.me/theorems/0044fcb0-f5d0-4d17-b0d6-d3d7ce416661
-- title:
--   cappedJumpSumAt succ eq add gamma
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_add_gamma` is extracted from `LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F001

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

theorem _root_.LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_add_gamma (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hθ : Function.Injective θ)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ}
    (hlt : LevyStochCalc.Poisson.jumpTime N A k ω
      < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω)
    (hle : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)) :
    ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
      cappedJumpSumAt X Y A T (k + 1) ω
        = cappedJumpSumAt X Y A T k ω + coeffs.γ (θ j) (Y (θ j) ω) (ε j) := by sorry
