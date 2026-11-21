-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_charPairing_eq_zero
-- name    : LevyStochCalc.Poisson.charPairing_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:17:31.123846+00:00
-- url     : https://prove2.me/theorems/90da418d-c687-4e57-a4c9-87ed3cb83622
-- title:
--   charPairing eq zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.charPairing_eq_zero` is extracted from `LevyStochCalc.Poisson.CharacterVanish`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterVanish_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the characters vanishes

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is
bounded by `2 ν(A)` times its own running integral, so the Grönwall iteration makes it vanish on
`[0, T]`. The weight is therefore orthogonal to the character of every finite family of window
sets inside `(0, T] × A`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Poisson.charPairing_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    charPairing N w Bfam r t = 0 := by sorry
