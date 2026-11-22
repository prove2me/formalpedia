-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_ae_forall_jumpSum_eq_cappedJumpSum
-- name    : LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSum_eq_cappedJumpSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:23:57.07161+00:00
-- url     : https://prove2.me/theorems/0f7fa985-876a-4345-9806-09e651a94580
-- title:
--   ae forall jumpSum eq cappedJumpSum
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSum_eq_cappedJumpSum` is extracted from `LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump side of the finite-activity Itô–Lévy formula

Capping the arrival times of a mark set at the horizon leaves an increasing chain of stopping
times starting at the origin, and strictly between two consecutive capped arrival times the
accumulated jumps are constant, so the jump path is its continuous part translated by them. The
jump sum of the telescope over that chain is therefore the sum, over the strictly monotone
enumeration of the window's atom times, of the increments of the state function across the jumps,
read at the left limits of the path, both for the state coordinates themselves and after
prepending coordinates to them.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedChain

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

variable {N A}

theorem _root_.LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSum_eq_cappedJumpSum
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      ∀ i : Fin n, LevyStochCalc.Ito.JumpSplitting.jumpSum X A s ω i
        = cappedJumpSum X A T k ω i := by sorry
