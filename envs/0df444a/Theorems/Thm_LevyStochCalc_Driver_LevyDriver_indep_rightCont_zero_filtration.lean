-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_indep_rightCont_zero_filtration
-- name    : LevyStochCalc.Driver.LevyDriver.indep_rightCont_zero_filtration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T10:04:49.025661+00:00
-- url     : https://prove2.me/theorems/e73da878-777e-4f37-a18e-17ce011d0c2e
-- title:
--   indep rightCont zero filtration
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.indep_rightCont_zero_filtration` is extracted from `LevyStochCalc.Driver.GermIndep`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_GermIndep_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The germ field of a Lévy driver

`Driver/ValueSigma.lean` gives the independence of `ℱ₊ 0` from the driver's data along a strictly
increasing grid of positive times. An arbitrary finite family of positive times is put in that
form by sorting it (`gridOf`), which turns the statement into one about arbitrary finite tuples.
Independence then passes to the supremum over finite subfamilies of the generators of `ℱ T`
(`indep_iSup_of_finset`), the two generators outside reach — Brownian values at non-positive times
and the part of a region in negative time — being almost surely constant and so dropping out.

## Main statements

* `LevyDriver.indep_valueTuple` — `ℱ₊ 0` against an arbitrary finite tuple of the driver's data.
* `LevyDriver.indep_rightCont_zero_filtration` — `ℱ₊ 0` against `ℱ T` for every `T > 0`.
* `LevyDriver.isTrivialSigma_rightCont_zero` — Blumenthal's 0-1 law itself.
* `LevyDriver.condExp_rightCont_nonpos` — the conditional expectation on `ℱ₊ s`, `s ≤ 0`, is the
  mean.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

theorem _root_.LevyStochCalc.Driver.LevyDriver.indep_rightCont_zero_filtration {T : ℝ} (hT : 0 < T) :
    Indep (D.filtration.rightCont 0) (D.filtration T) P := by sorry
