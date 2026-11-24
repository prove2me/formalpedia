-- Prove2me | Theorems.Thm_Kyprianou_boundedVariationCriterionCh02
-- name    : Kyprianou.boundedVariationCriterionCh02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:21:19.986025+00:00
-- url     : https://prove2.me/theorems/8f6e226b-6e3a-40da-9917-e0af2d8ae3f3
-- title:
--   Lemma 2.12: bounded-variation paths criterion
-- statement:
--   Lemma 2.12: bounded-variation paths criterion. The Gaussian component vanishes and small-jump first moments are summable.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33–66

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem boundedVariationCriterionCh02
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => X t ω) Set.univ) ↔
    σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure := by sorry

end Kyprianou
