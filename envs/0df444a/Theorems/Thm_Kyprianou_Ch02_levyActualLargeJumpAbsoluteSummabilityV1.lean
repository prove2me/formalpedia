-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyActualLargeJumpAbsoluteSummabilityV1
-- name    : Kyprianou.Ch02.levyActualLargeJumpAbsoluteSummabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:10:19.743873+00:00
-- url     : https://prove2.me/theorems/7f2f3575-9c6b-4242-88f8-bee77a804319
-- title:
--   Finite absolute sum of genuine original large Levy jumps on every compact horizon
-- statement:
--   For the original real cadlag Levy process, the actual jump weights with absolute magnitude greater than one form a finite set on each compact positive-time interval, and their absolute sum is therefore finite. No truncated moment condition is needed. Reuse the proved generic Avram cadlag finite-large-jump-support lemma; derive its right and left path hypotheses from the given IsLevyProcess cadence on a full-measure event.
-- source:
--   Kyprianou (2006), Chapter 2: large-jump finite-activity property and small-jump first-moment compensator in Lemma 2.12.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyActualLargeJumpAbsoluteSummabilityV1
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
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        if (1 : ℝ) < |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| then |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| else 0) := by
  sorry
