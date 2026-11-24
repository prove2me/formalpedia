-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPhysicalSmallJumpMassAEMeasurableV1
-- name    : Kyprianou.Ch02.levyPhysicalSmallJumpMassAEMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:11:52.144715+00:00
-- url     : https://prove2.me/theorems/e436c662-f865-4aa6-9487-d6fece70778a
-- title:
--   Measurability of actual original Levy small-jump mass
-- statement:
--   Show that for the specified original Levy process the extended nonnegative sum of actual positive-time jumps of size at most one on each integer horizon is almost everywhere measurable. Use generic measurable enumeration of cadlag jump times and marks and a measurable original whole-path map, or independently prove the same fact. The theorem requires no finite first moment, absolute jump sum or bounded variation.
-- source:
--   Kyprianou (2006), Chapter 2: large-jump finite-activity property and small-jump first-moment compensator in Lemma 2.12.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyPhysicalSmallJumpMassAEMeasurableV1
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
    ∀ n : ℕ,
      AEMeasurable (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
           ENNReal.ofReal (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0)) P := by
  sorry
