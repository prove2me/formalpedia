-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_aestronglyMeasurable_cellHalf
-- name    : LevyStochCalc.Driver.aestronglyMeasurable_cellHalf
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:19:50.720413+00:00
-- url     : https://prove2.me/theorems/573a2c47-0efc-4397-a9aa-e825e15486e7
-- title:
--   aestronglyMeasurable cellHalf
-- statement:
--   The source theorem `LevyStochCalc.Driver.aestronglyMeasurable_cellHalf` is extracted from `LevyStochCalc.Driver.CellGronwallPairing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairings of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character, and equally the
cosine half plus `i` times the sine half, a half being the pairing of a trigonometric function of
the Brownian increment with the Poisson character. This file introduces those pairings together
with their integrability and boundedness, and records the cell identity for a real pairing in the
reduced form that the recombination consumes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Parts

variable (N : PoissonRandomMeasure P ν)

end Parts

section Half

variable (N : PoissonRandomMeasure P ν)

variable {Z V : Ω → ℝ} {Mv l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Driver.aestronglyMeasurable_cellHalf {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {b T : ℝ} (hT : 0 < T) (hbT : b < T) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A)
    {e₀ : E} (he₀ : e₀ ∈ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V) (hgc : Continuous g)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (T' : ℝ) :
    AEStronglyMeasurable (fun s => cellHalf N w Bfam Z V l X g s)
      (volume.restrict (Set.Icc (0 : ℝ) T')) := by sorry
