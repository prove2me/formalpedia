-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_forall_exp_windowSum_sub_one
-- name    : LevyStochCalc.Poisson.ae_forall_exp_windowSum_sub_one
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:35:46.238918+00:00
-- url     : https://prove2.me/theorems/1d186351-ff92-440f-8a39-4f941886d713
-- title:
--   ae forall exp windowSum sub one
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_forall_exp_windowSum_sub_one` is extracted from `LevyStochCalc.Poisson.ChainRule`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChainRule_F001

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

theorem _root_.LevyStochCalc.Poisson.ae_forall_exp_windowSum_sub_one (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (h : ℝ × E → ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
      (Complex.exp (Complex.I * (windowSum N B h T ω : ℂ)) - 1
        = ∫ p in B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
            Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω))
      ∧ (Complex.exp (Complex.I * (windowSumStrict N B h T ω : ℂ)) - 1
        = ∫ p in B ∩ Set.Ioo (0 : ℝ) T ×ˢ Set.univ,
            Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω)) := by sorry
