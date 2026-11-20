-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_exists_forall_count_timeSlab_le_one
-- name    : LevyStochCalc.Poisson.ae_exists_forall_count_timeSlab_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:54:43.247318+00:00
-- url     : https://prove2.me/theorems/c2ff2845-cd2c-46fc-8887-39f0eda0e140
-- title:
--   ae exists forall count timeSlab le one
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_exists_forall_count_timeSlab_le_one` is extracted from `LevyStochCalc.Poisson.Simplicity`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002

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

theorem _root_.LevyStochCalc.Poisson.ae_exists_forall_count_timeSlab_le_one (N : PoissonRandomMeasure.{u, v, w} P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ∀ k : ℕ, N.N ω (B ∩ timeSlab n k ×ˢ Set.univ) ≤ 1 := by sorry
