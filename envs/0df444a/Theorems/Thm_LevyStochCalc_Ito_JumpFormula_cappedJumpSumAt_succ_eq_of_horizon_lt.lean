-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_cappedJumpSumAt_succ_eq_of_horizon_lt
-- name    : LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_of_horizon_lt
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:56:24.236529+00:00
-- url     : https://prove2.me/theorems/610a7603-d159-4dba-99eb-cd790a57d0b4
-- title:
--   cappedJumpSumAt succ eq of horizon lt
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_of_horizon_lt` is extracted from `LevyStochCalc.Ito.JumpFormulaGeneralShiftAtomSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The telescope's jump sum over a prescribed evaluation path

Over an enumeration of the atoms of a window, the telescope of a state function along the chain
of capped jump sums collapses to the sum, over those atoms, of the increments of the state
function taken at the left limits of the jump path and displaced by the jump coefficient read at
the prescribed states: an index whose arrival time has passed the horizon contributes nothing and
each in-window index contributes one increment. Almost surely every window carries such an
enumeration, which gives that identification for the path itself and for a path translated by the
jump sum, together with the piecewise translation and the atom sum for the jump sums evaluated at
the point values and at the left limits of the path.
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

section JumpSideAssembly

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

theorem _root_.LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_of_horizon_lt (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ} (hk : ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω) :
    cappedJumpSumAt X Y A T (k + 1) ω = cappedJumpSumAt X Y A T k ω := by sorry
