-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_exp_windowSum_sub_one_of_repr
-- name    : LevyStochCalc.Poisson.exp_windowSum_sub_one_of_repr
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:57:14.720552+00:00
-- url     : https://prove2.me/theorems/bf611b06-c7be-4da8-b996-303951093da1
-- title:
--   exp windowSum sub one of repr
-- statement:
--   The source theorem `LevyStochCalc.Poisson.exp_windowSum_sub_one_of_repr` is extracted from `LevyStochCalc.Poisson.ChainRule`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChainRule_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump chain rule for a Poisson random measure

A product over a finite set whose factors are ordered by a key telescopes: the product minus one
is the sum, over the factors, of the product of the earlier ones times the increment of that
factor. On a set of finite reference intensity a Poisson random measure is a finite sum of unit
masses at distinct times, so the exponential of an integral against it obeys that telescoping,
which is the chain rule the exponential family needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

section Telescope

variable {α : Type*} [DecidableEq α] {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]

end Telescope

section Pathwise

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [MeasurableSpace.CountablyGenerated E] in
open scoped Classical in

theorem _root_.LevyStochCalc.Poisson.exp_windowSum_sub_one_of_repr (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (h : ℝ × E → ℝ) {J : Set ℝ} (hJm : MeasurableSet J)
    (hJ0 : J ⊆ Set.Ioi 0) (hJ : ∀ u ∈ J, Set.Ioo (0 : ℝ) u ⊆ J) (ω : Ω)
    (hsrepex : ∃ s : Finset (ℝ × E), (N.N ω).restrict (B ∩ J ×ˢ Set.univ)
      = ∑ p ∈ s, ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)) {p} • Measure.dirac p)
    (hn : ∃ k : ℕ, N.N ω (B ∩ J ×ˢ Set.univ) = k)
    (hIV : Probability.IsIntegerValued ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)))
    (hsimple : ∀ t : ℝ, N.N ω (B ∩ ({t} : Set ℝ) ×ˢ Set.univ) ≤ 1) :
    Complex.exp (Complex.I * ((∫ p in B ∩ J ×ˢ Set.univ, h p ∂(N.N ω) : ℝ) : ℂ)) - 1
      = ∫ p in B ∩ J ×ˢ Set.univ,
          Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by sorry
