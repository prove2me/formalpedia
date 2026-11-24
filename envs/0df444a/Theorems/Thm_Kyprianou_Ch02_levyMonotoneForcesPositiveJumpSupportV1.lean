-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyMonotoneForcesPositiveJumpSupportV1
-- name    : Kyprianou.Ch02.levyMonotoneForcesPositiveJumpSupportV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:34:31.869489+00:00
-- url     : https://prove2.me/theorems/30658ee3-1cb6-41ef-8669-de14bbfc45a7
-- title:
--   Monotone Lévy paths exclude negative jump intensity
-- statement:
--   Monotone paths have no negative physical jumps. Alternatively transfer nonnegative small-time marginal support to the Lévy measure via a compactly supported negative-side test and the small-time extraction/uniqueness theorem.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; necessity of the subordinator triplet conditions.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyMonotoneForcesPositiveJumpSupportV1
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
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) :
    levyMeasure (Set.Iio (0 : ℝ)) = 0 := by
  sorry
