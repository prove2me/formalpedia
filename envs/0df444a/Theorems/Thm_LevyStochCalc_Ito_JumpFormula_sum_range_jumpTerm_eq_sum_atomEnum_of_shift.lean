-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_sum_range_jumpTerm_eq_sum_atomEnum_of_shift
-- name    : LevyStochCalc.Ito.JumpFormula.sum_range_jumpTerm_eq_sum_atomEnum_of_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:29:06.493716+00:00
-- url     : https://prove2.me/theorems/c9f14e2c-21af-44b7-9d88-d251a5b8ef1d
-- title:
--   sum range jumpTerm eq sum atomEnum of shift
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTerm_eq_sum_atomEnum_of_shift` is extracted from `LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F001

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

end CappedChain

section JumpSideAssembly

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

theorem _root_.LevyStochCalc.Ito.JumpFormula.sum_range_jumpTerm_eq_sum_atomEnum_of_shift {N' : ℕ} (f : (Fin N' → ℝ) → ℝ)
    {V Y : ℝ → Ω → Fin N' → ℝ} {c : ℕ → Ω → Fin N' → ℝ} {jump : Fin K → Fin N' → ℝ} {m : ℕ}
    (hmonoθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    (hV : Continuous fun t => V t ω)
    (hstrict : ∀ i : ℕ, LevyStochCalc.Poisson.jumpTime N A (i + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      LevyStochCalc.Poisson.jumpTime N A i ω < LevyStochCalc.Poisson.jumpTime N A (i + 1) ω)
    (hshift : ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω → V s ω + c k ω = Y s ω)
    (hczero : ∀ k : ℕ, ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω →
      c (k + 1) ω = c k ω)
    (hcinc : ∀ k : ℕ, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ)
        ∧ c (k + 1) ω = c k ω + jump j)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => Y s ω) (θ j) + jump j)
          - f (Function.leftLim (fun s => Y s ω) (θ j))) := by sorry
