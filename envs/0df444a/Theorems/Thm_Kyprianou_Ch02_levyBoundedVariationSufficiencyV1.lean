-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyBoundedVariationSufficiencyV1
-- name    : Kyprianou.Ch02.levyBoundedVariationSufficiencyV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:54:19.585214+00:00
-- url     : https://prove2.me/theorems/a57c73c7-1edf-401f-8dbb-b935fdc7c5f9
-- title:
--   Sufficiency in Lévy bounded-variation criterion: drift plus absolutely summable jumps
-- statement:
--   For a genuine Lévy process with zero Gaussian coefficient and integrable truncated first jump moment, its sample paths have locally bounded variation almost surely. Show its Lévy-Itô representation is deterministic linear drift plus an absolutely convergent sum of jumps on each compact time interval; transfer this path property to the original process using a process-level equivalence with a joint cadlag modification. Exact source assumes no extraneous finite-activity condition.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyBoundedVariationSufficiencyV1
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
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) := by
  sorry
