-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_PicardOutput_toSolvesBSDEJ
-- name    : LevyStochCalc.BSDEJ.Solves.PicardOutput.toSolvesBSDEJ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:08:46.26868+00:00
-- url     : https://prove2.me/theorems/f65a6f79-1124-42cb-a7f4-0a148dfb9a84
-- title:
--   toSolvesBSDEJ
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.PicardOutput.toSolvesBSDEJ` is extracted from `LevyStochCalc.BSDEJ.PicardStep`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardStep_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One Picard step of a backward equation with jumps

The Picard map of a backward equation with jumps sends a triple `(Y', Z', U')` to the triple
solving the equation whose generator is frozen along the input, that is to the martingale
representation of the terminal datum `ξ + ∫_0^T b_s ds` for `b = f(·, Y', Z', U')`.
`PicardOutput` is the predicate satisfied by the output triple: the fields of `SolvesBSDEJ` with
the drift integral taken along the input triple, together with the terminal value of `Y` and its
finite `S²` seminorm. A fixed point of the map, that is a `PicardOutput` whose input and output
triples agree, solves the backward equation.

The output is built from the martingale representation of the centred terminal datum
(`exists_picard_integrands_of_rightCont`), the everywhere-càdlàg versions of the two stochastic
legs (`exists_cadlag_brownianLeg`, `exists_cadlag_poissonLeg`) and the primitive of the drift
(`driftLeg`), as `Y_t = c + M^W_t + M^N_t − ∫_0^t b_s ds` with `c` the mean of the terminal
datum.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.PicardOutput` — the output triple of one Picard step.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.toSolvesBSDEJ` — a fixed point of the Picard step
  solves the backward equation.
* `LevyStochCalc.BSDEJ.Solves.measurable_biSup_sq_of_rightContinuous` — the squared running
  supremum of a right-continuous process with measurable slices is measurable.
* `LevyStochCalc.BSDEJ.Solves.exists_picardOutput` — the Picard step has an output triple.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### The output of a Picard step -/

theorem _root_.LevyStochCalc.BSDEJ.Solves.PicardOutput.toSolvesBSDEJ {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : PicardOutput D f ξ T Y Z U Y Z U) :
    SolvesBSDEJ D f ξ T Y Z U := by sorry
