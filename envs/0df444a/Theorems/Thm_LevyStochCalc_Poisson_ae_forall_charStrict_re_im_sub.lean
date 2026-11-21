-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_forall_charStrict_re_im_sub
-- name    : LevyStochCalc.Poisson.ae_forall_charStrict_re_im_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:55:26.003291+00:00
-- url     : https://prove2.me/theorems/388a4ee6-c5a1-47ba-9291-bf52c9fe2155
-- title:
--   ae forall charStrict re im sub
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_forall_charStrict_re_im_sub` is extracted from `LevyStochCalc.Poisson.CharacterCell`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrict_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a window family as a pure-jump process

For a finite family of window sets inside `(a, b] × A`, the real and imaginary parts of the
character `charAt` of the counts up to `s` are bounded by one, are measurable at time `s` for a
Poisson filtration, and, outside one null set, satisfy at every time the jump identity
`Y s = Y a + ∫_{(a, s] × A} g dN` whose weight `g` is the corresponding part of
`exp (i · windowSumStrict) (exp (i · mark) − 1)`, bounded by two. This is the shape the product
rule for a continuous Itô process and a pure-jump process asks for.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Jump

section Predictable

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
  {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

include hBm hA hAν hBsub in

theorem _root_.LevyStochCalc.Poisson.ae_forall_charStrict_re_im_sub (hℱ : IsPoissonFiltration N ℱ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ,
      ((charStrict N w Bfam s ω).re = (charAt N w Bfam 0 ω).re
          + ∫ q in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
              charRe N w Bfam A T ω q.1 q.2 ∂(N.N ω))
        ∧ ((charStrict N w Bfam s ω).im = (charAt N w Bfam 0 ω).im
          + ∫ q in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
              charIm N w Bfam A T ω q.1 q.2 ∂(N.N ω)) := by sorry
