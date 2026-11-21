-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_le_aug_of_indep_of_le_sup
-- name    : LevyStochCalc.Probability.le_aug_of_indep_of_le_sup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:16:31.0366+00:00
-- url     : https://prove2.me/theorems/5f2cd374-8014-46e4-bafc-b00975db6841
-- title:
--   le aug of indep of le sup
-- statement:
--   The source theorem `LevyStochCalc.Probability.le_aug_of_indep_of_le_sup` is extracted from `LevyStochCalc.Driver.AugJointRightCont`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right-continuity of the augmented joint filtration of a Lévy driver

Write `𝔸 = augFiltration D.filtration P` for the `0`-clamped augmentation of the joint filtration
of a Lévy driver. Its germ field at a time `t ≥ 0` is already its field at `t`.

The driver's data over `(t, T]` measured from `t` — the Brownian increments `W u - W t` for
`u ∈ (t, T]` and the counts on the measurable regions inside `(t, T] × E` — generates the
σ-algebra `futureSigma t T`. Joined with `ℱ t` it contains `ℱ T`, and it is independent of the
germ field `ℱ₊ t`, the independence coming from the data of a grid starting at `t`. A σ-algebra
that contains `ℱ t`, sits inside the join `ℱ t ⊔ futureSigma t T` and is independent of
`futureSigma t T` differs from `ℱ t` only by null sets: the conditional expectation on `ℱ t` of
the indicator of one of its sets is that indicator, because the two integrate alike over the
π-system of intersections generating the join. Hence `ℱ₊ t ≤ aug (ℱ t)`, and since augmentation
commutes with the countable antitone infimum `⨅ n, ℱ (t + (n + 1)⁻¹)` this gives `𝔸₊ t = 𝔸 t`.
Below time `0` the filtration `𝔸` is constant, so `𝔸` is right-continuous.

## Main statements

* `LevyStochCalc.Probability.le_aug_of_indep_of_le_sup` — the σ-algebra criterion for lying in
  an augmentation.
* `LevyStochCalc.Driver.LevyDriver.filtration_le_sup_futureSigma` — `ℱ T ≤ ℱ t ⊔ futureSigma t T`.
* `LevyStochCalc.Driver.LevyDriver.indep_futureSigma_rightCont` — `futureSigma t T` against
  `ℱ₊ t`.
* `LevyStochCalc.Driver.LevyDriver.filtration_rightCont_le_aug` — `ℱ₊ t ≤ aug (ℱ t)`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_le_self` — `𝔸₊ t ≤ 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_eq` — `𝔸₊ t = 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.isRightContinuous_augFiltration` — `𝔸` is right-continuous.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Probability.le_aug_of_indep_of_le_sup {𝒜 𝒢 𝒞 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (h𝒢 : 𝒢 ≤ mΩ)
    (h𝒜𝒞 : 𝒜 ≤ 𝒞) (h𝒞 : 𝒞 ≤ 𝒜 ⊔ 𝒢) (hind : Indep 𝒞 𝒢 P) :
    𝒞 ≤ aug 𝒜 mΩ P := by sorry
