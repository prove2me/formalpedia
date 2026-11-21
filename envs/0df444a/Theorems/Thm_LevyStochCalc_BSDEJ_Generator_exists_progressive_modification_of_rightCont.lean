-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Generator_exists_progressive_modification_of_rightCont
-- name    : LevyStochCalc.BSDEJ.Generator.exists_progressive_modification_of_rightCont
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:51:13.045209+00:00
-- url     : https://prove2.me/theorems/5e0c6dff-7274-441f-84a0-3f3a6f9d83be
-- title:
--   exists progressive modification of rightCont
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Generator.exists_progressive_modification_of_rightCont` is extracted from `LevyStochCalc.BSDEJ.DriftModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressive modification of a drift progressive for the right-continuous filtration

A real process that is progressively measurable for the right-continuous filtration `ℱ₊` has a
modification, equal to it almost everywhere on `Ω × [0, T]`, that is progressively measurable for
`ℱ` itself. The modification is the pointwise `limsup` of the moving averages of the process over
the windows `[s - 2c, s - c]` lying strictly to the left of `s`: each such average is
`ℱ`-progressive because it reads the process only before `s`, and Lebesgue's differentiation
theorem identifies the limit with the process at almost every time.
-/

open MeasureTheory Filter Metric
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### Moving averages over a window strictly to the left -/

/-! ### Lebesgue differentiation along the left windows -/

/-! ### The modification -/

theorem _root_.LevyStochCalc.BSDEJ.Generator.exists_progressive_modification_of_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∃ b' : Ω → ℝ → ℝ, Measurable (Function.uncurry b') ∧
      Probability.ProgressivelyMeasurable ℱ b' ∧
      (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b' ω s = 0) ∧ Brownian.Ito.energy P T b' ≠ ⊤ ∧
      ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), b' p.1 p.2 = b p.1 p.2 := by sorry
