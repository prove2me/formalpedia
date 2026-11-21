-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_PicardOutput_isItoLevyProcess_clampT
-- name    : LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:16:25.797164+00:00
-- url     : https://prove2.me/theorems/743fcb3b-c5b5-40bf-9c89-86a4f201be89
-- title:
--   isItoLevyProcess clampT
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT` is extracted from `LevyStochCalc.BSDEJ.PicardItoLevy`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardItoLevy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy decomposition of a Picard output

The output `Y` of a Picard step satisfies the backward equation on the horizon `[0, T]` only.
Frozen at the horizon, `t ↦ Y (min t T)`, it carries an Itô–Lévy decomposition at every
nonnegative time, with drift `-b` for a drift `b` that is almost everywhere the generator along
the input triple, diffusion vector `Z` and jump integrand `U`: subtracting the backward equation
at `t` from the backward equation at `0` turns the remaining window `[t, T]` of the drift
integral into the initial window `[0, t]`, and past the horizon neither the drift integral nor
either stochastic leg moves.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.clampT` — a process frozen at the horizon.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.clampT_decomposition_of_eqn` — the decomposition of a frozen path
  satisfying the backward equation, for abstract stochastic legs.
* `LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT` — the frozen Picard output
  is an Itô–Lévy process.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Freezing a process at the horizon -/

/-! ### The drift integral past the horizon -/

/-! ### The decomposition of a frozen backward path -/

/-! ### The frozen Picard output -/

theorem _root_.LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y' : ℝ → Ω → ℝ}
    {Z' : ℝ → Ω → (Fin d → ℝ)} {U' : ℝ → Ω → E → ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : PicardOutput D f ξ T Y' Z' U' Y Z U) (hT : 0 < T)
    {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hb : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b p.1 p.2 = f p.2 (Y' p.2 p.1) (Z' p.2 p.1) (U' p.2 p.1)) :
    LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N (augJoint D)
      D.isBrownianFiltration_aug D.isPoissonFiltration_aug (clampT T Y) (Y 0)
      (fun s ω => -b ω s) Z (fun ω s e => U s ω e) := by sorry
