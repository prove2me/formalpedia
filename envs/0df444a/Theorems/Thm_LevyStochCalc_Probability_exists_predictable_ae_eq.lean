-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exists_predictable_ae_eq
-- name    : LevyStochCalc.Probability.exists_predictable_ae_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:04:51.569206+00:00
-- url     : https://prove2.me/theorems/de85b881-03ef-40c2-b36f-6a443b33e5f0
-- title:
--   exists predictable ae eq
-- statement:
--   The source theorem `LevyStochCalc.Probability.exists_predictable_ae_eq` is extracted from `LevyStochCalc.Probability.PredictableModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Probability_PredictableModification_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of progressive integrands

The elementary integrands of the `L²` theory — finite sums of a coefficient measurable at the
left endpoint of a cell, carried on that cell — are predictable, and the predictable processes
are closed under pointwise upper limits. Since the elementary integrands are dense in the
progressive integrands of finite energy, a progressive integrand agrees with a predictable one
almost everywhere in time and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Cells

end Cells

section Modification

open Brownian.Ito

variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Probability.exists_predictable_ae_eq (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : ProgressivelyMeasurable ℱ H)
    {T : ℝ} (hT : 0 < T) (hfin : energy P T H ≠ ⊤) :
    ∃ K : Ω → ℝ → ℝ, Predictable ℱ K ∧
      (fun p : Ω × ℝ => H p.1 p.2) =ᵐ[energyMeasure P T] fun p : Ω × ℝ => K p.1 p.2 := by sorry
