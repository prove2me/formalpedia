-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverJointInfinitePiLaw
-- name    : Kyprianou.Ch01.compoundPoissonDriverJointInfinitePiLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:09:37.534072+00:00
-- url     : https://prove2.me/theorems/c0ea4643-f132-4748-a90d-b65b9d75fc83
-- title:
--   Full marked compound-Poisson sequence law equals the joint infinite product measure
-- statement:
--   Under the full joint iIndepFun compound-Poisson driver, the complete sequence of interarrival times and marks, indexed by the disjoint sum of naturals, has the infinite product distribution of the exponential holding-time and jump-mark marginal laws.
-- source:
--   LeanLevy compound Poisson driver joint independence, Mathlib ProbabilityTheory.iIndepFun.hasLaw_infinitePi. Used to factor first-event and shifted-tail law for Kyprianou (2006) Section 1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonDriverJointInfinitePiLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    HasLaw (fun w (i : ℕ ⊕ ℕ) => (Sum.elim arrival marks i) w)
      (Measure.infinitePi
        (Sum.elim (fun _ : ℕ => expMeasure rate)
                  (fun _ : ℕ => jumpLaw))) Q := by
  sorry
