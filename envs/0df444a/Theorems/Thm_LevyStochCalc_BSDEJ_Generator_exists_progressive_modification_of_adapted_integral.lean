-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Generator_exists_progressive_modification_of_adapted_integral
-- name    : LevyStochCalc.BSDEJ.Generator.exists_progressive_modification_of_adapted_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:21:09.682518+00:00
-- url     : https://prove2.me/theorems/f658e475-7814-4ee8-ab1d-18c8616d0894
-- title:
--   exists progressive modification of adapted integral
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Generator.exists_progressive_modification_of_adapted_integral` is extracted from `LevyStochCalc.BSDEJ.ProgressiveDrift`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_ProgressiveDrift_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressive modification of a drift with an adapted primitive

Let `φ : Ω → ℝ → ℝ` be jointly measurable, of finite energy on `[0, T]` and vanishing off it, and
suppose that for every `t ∈ [0, T]` the primitive `ω ↦ ∫_0^t φ_s(ω) ds` agrees almost surely with
a function measurable for the right-continuous filtration `ℱ_{t+}`. If `ℱ_0` contains the `P`-null
sets, then `φ` has a modification `φ̃` that is progressively measurable for `ℱ` itself and agrees
with `φ` almost everywhere for `P ⊗ ds` on `Ω × [0, T]`. The hypothesis bears on the primitive
of `φ`, where `exists_progressive_modification_of_rightCont` asks `φ` itself to be progressive for
the right-continuous filtration.

Cut `φ` and its primitive to the `ℱ_0`-measurable, `P`-conull set of sample points with an
integrable path. The cut primitive `A_t = ∫_0^t φ_s ds` (the drift leg) is then
`ℱ_{t+}`-measurable at every time and has continuous paths, so the difference quotient
`c⁻¹ (A_{s − c} − A_{s − 2c})` — the mean of the cut drift over the window `[s − 2c, s − c]` —
reads `A` only at times strictly before `s` and is `ℱ`-progressive. The modification `φ̃` is the
`limsup` of these means as `c ↓ 0`, cut to `[0, T]`, and Lebesgue's differentiation theorem
identifies it with `φ` at almost every time of almost every path.

## Main statements

* `stronglyMeasurable_driftLeg_of_aestronglyMeasurable`: the drift leg is measurable for the
  right-continuous filtration at every time.
* `leftAverage_indicator_eq`: the window mean of the cut drift is a difference quotient of the
  drift leg.
* `progressivelyMeasurable_leftAverage_indicator`: the window means of the cut drift are
  `ℱ`-progressive.
* `exists_progressive_modification_of_adapted_integral`: the progressive modification.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {φ : Ω → ℝ → ℝ} {T : ℝ}

theorem _root_.LevyStochCalc.BSDEJ.Generator.exists_progressive_modification_of_adapted_integral (hφm : Measurable (Function.uncurry φ))
    (hφz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0) (hφq : Brownian.Ito.energy P T φ ≠ ⊤)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEStronglyMeasurable[ℱ.rightCont t] (fun ω => ∫ s in Set.Icc (0 : ℝ) t, φ ω s) P)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T) :
    ∃ φ' : Ω → ℝ → ℝ, Measurable (Function.uncurry φ') ∧
      Probability.ProgressivelyMeasurable ℱ φ' ∧
      (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ' ω s = 0) ∧
      Brownian.Ito.energy P T φ' = Brownian.Ito.energy P T φ ∧
      ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), φ' p.1 p.2 = φ p.1 p.2 := by sorry
