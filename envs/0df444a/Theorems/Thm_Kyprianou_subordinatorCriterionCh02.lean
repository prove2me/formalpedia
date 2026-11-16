-- Prove2me | Theorems.Thm_Kyprianou_subordinatorCriterionCh02
-- name    : Kyprianou.subordinatorCriterionCh02
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:22:10.049049+00:00
-- url     : https://prove2.me/theorems/a80832e8-38dd-405f-ad3c-9dcd28a22956
-- title:
--   Lemma 2.14: subordinator path criterion
-- statement:
--   Lemma 2.14: subordinator path criterion. Nonnegative paths' increments correspond to nonnegative finite-variation drift.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33–66

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem subordinatorCriterionCh02
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
    (∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) ↔
    levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a + ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by sorry

end Kyprianou
