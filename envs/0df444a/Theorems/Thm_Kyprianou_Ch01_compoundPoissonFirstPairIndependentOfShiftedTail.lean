-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstPairIndependentOfShiftedTail
-- name    : Kyprianou.Ch01.compoundPoissonFirstPairIndependentOfShiftedTail
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:13:46.421398+00:00
-- url     : https://prove2.me/theorems/84542092-a6b1-4b9a-8905-4a115cf3589c
-- title:
--   The first marked exponential holding time is independent of the infinite shifted driver tail
-- statement:
--   The random pair consisting of the first exponential holding time and first jump mark is independent, as an entire measurable random variable, of the infinite pair of sequences of all later interarrivals and marks. Derive by splitting the jointly independent Sum-indexed family into finite head and infinite tail and applying product-space cylinder independence.
-- source:
--   Joint iid compound-Poisson driver, Kyprianou (2006), Section 1.3.4; needed to condition the one-time reverse-Lamperti distribution on first holding time and offspring mark.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstPairIndependentOfShiftedTail
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q := by
  sorry
