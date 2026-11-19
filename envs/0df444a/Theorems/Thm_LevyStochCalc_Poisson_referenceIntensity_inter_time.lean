-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_referenceIntensity_inter_time
-- name    : LevyStochCalc.Poisson.referenceIntensity_inter_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:28:56.828205+00:00
-- url     : https://prove2.me/theorems/6965e8d9-0b5c-4b3c-9ebc-fe7d8bd1300d
-- title:
--   referenceIntensity inter time
-- statement:
--   The source theorem `LevyStochCalc.Poisson.referenceIntensity_inter_time` is extracted from `LevyStochCalc.Poisson.Simplicity`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

end Tail

section Mesh

end Mesh

section Simple

theorem _root_.LevyStochCalc.Poisson.referenceIntensity_inter_time {B : Set (ℝ × E)} (hB : MeasurableSet B) {S : Set ℝ}
    (hS : MeasurableSet S) :
    referenceIntensity ν (B ∩ S ×ˢ Set.univ) = ∫⁻ x in S, sectionDensity ν B x := by sorry
