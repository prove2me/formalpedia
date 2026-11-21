-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_norm_charPairing_le_integral
-- name    : LevyStochCalc.Poisson.norm_charPairing_le_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:14:28.413378+00:00
-- url     : https://prove2.me/theorems/10182985-4498-4dcc-92a2-73359a980cbc
-- title:
--   norm charPairing le integral
-- statement:
--   The source theorem `LevyStochCalc.Poisson.norm_charPairing_le_integral` is extracted from `LevyStochCalc.Poisson.CharacterGronwall`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterGronwall_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the characters satisfies a Grönwall inequality

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is a
window integral of the marks times the pairings at earlier times. Its norm is therefore bounded by
`2 ν(A)` times its own running integral, and it is a bounded measurable function of the time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Pairing

end Pairing

section Bound

theorem _root_.LevyStochCalc.Poisson.norm_charPairing_le_integral (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    (hAne : A.Nonempty) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖charPairing N w Bfam r t‖
      ≤ 2 * (ν A).toReal * ∫ s in (0 : ℝ)..t, ‖charPairing N w Bfam r s‖ := by sorry
