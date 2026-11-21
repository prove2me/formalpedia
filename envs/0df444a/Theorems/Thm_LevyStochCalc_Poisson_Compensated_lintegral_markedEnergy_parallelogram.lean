-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_lintegral_markedEnergy_parallelogram
-- name    : LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_parallelogram
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:12:58.177535+00:00
-- url     : https://prove2.me/theorems/0c6a2033-3d6d-4efd-b294-fbe2dc23a66a
-- title:
--   lintegral markedEnergy parallelogram
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_parallelogram` is extracted from `LevyStochCalc.Poisson.CompensatedLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the compensated Poisson integral

The compensated integral is built as an `L²` limit of elementary integrals, which is not itself a
linear construction, so linearity comes from the isometries instead: they fix every squared
`L²`-distance among the integrals of two integrands and of their sum, and the parallelogram law
for the marked energies then forces the sum relation. The same three-distance argument gives the
scalar rule.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Parallelogram

variable {φ₁ φ₂ : Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_parallelogram
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e)
        + markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e)
      = 2 * markedEnergy P ν T φ₁ + 2 * markedEnergy P ν T φ₂ := by sorry
