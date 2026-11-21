-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_ae_exists_tendsto_cadlagCondExp_nhdsLT
-- name    : LevyStochCalc.Driver.LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T10:53:24.857503+00:00
-- url     : https://prove2.me/theorems/533508b3-db75-462e-b370-01ae45583328
-- title:
--   ae exists tendsto cadlagCondExp nhdsLT
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT` is extracted from `LevyStochCalc.Driver.CadlagMartingale`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CadlagMartingale_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg conditional-expectation martingale of a Lévy driver

`Probability/CondExpModification.lean` builds a right-continuous modification of
`t ↦ 𝔼[ξ | ℱ₊ t]` indexed by `ℝ≥0`, the index type the càdlàg machinery needs. Reindexing by `ℝ`
means saying what happens before time `0`, where the constant `𝔼 ξ` is the right answer: it is
`𝔼[ξ | ℱ₊ t]` there by Blumenthal's 0-1 law (`Driver/GermIndep.lean`), and being constant it is
measurable for every σ-algebra, which the modification's value at `0` is not.

## Main statements

* `LevyDriver.cadlagCondExp` — the reindexed process.
* `LevyDriver.martingale_cadlagCondExp` — it is a martingale for `ℱ₊`.
* `LevyDriver.cadlagCondExp_ae_eq` — it agrees with `𝔼[ξ | ℱ₊ t]` at every fixed `t`.
* `LevyDriver.tendsto_cadlagCondExp_nhdsGT`, `LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT`
  — right continuity of every path, and left limits almost surely.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν) (ξ : Ω → ℝ)

variable {D ξ}

theorem _root_.LevyStochCalc.Driver.LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ L : ℝ,
      Tendsto (fun s => D.cadlagCondExp ξ s ω) (𝓝[<] t) (𝓝 L) := by sorry
