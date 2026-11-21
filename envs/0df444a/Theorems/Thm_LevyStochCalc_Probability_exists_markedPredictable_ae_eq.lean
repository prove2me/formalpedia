-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exists_markedPredictable_ae_eq
-- name    : LevyStochCalc.Probability.exists_markedPredictable_ae_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:33:44.178282+00:00
-- url     : https://prove2.me/theorems/b8272277-7397-4096-9e32-20418925c4bb
-- title:
--   exists markedPredictable ae eq
-- statement:
--   The source theorem `LevyStochCalc.Probability.exists_markedPredictable_ae_eq` is extracted from `LevyStochCalc.Probability.MarkedPredictableModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of marked progressive integrands

A mark-step integrand adapted at the left endpoints of its cells is predictable on the time–mark
space, and the marked predictable processes are closed under pointwise upper limits. The
mark-step integrands are dense in the marked progressive integrands of finite energy, so such an
integrand agrees with a predictable one almost everywhere in time, mark and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ mΩ}

open LevyStochCalc.Poisson.Compensated

variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Probability.exists_markedPredictable_ae_eq (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : MarkedProgressivelyMeasurable ℱ φ) {T : ℝ} (hT : 0 < T)
    (hfin : markedEnergy P ν T φ ≠ ⊤) :
    ∃ ψ : Ω → ℝ → E → ℝ, MarkedPredictable ℱ ν ψ ∧
      (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
        =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by sorry
