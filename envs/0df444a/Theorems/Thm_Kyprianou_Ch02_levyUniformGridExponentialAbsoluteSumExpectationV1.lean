-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyUniformGridExponentialAbsoluteSumExpectationV1
-- name    : Kyprianou.Ch02.levyUniformGridExponentialAbsoluteSumExpectationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:34.173348+00:00
-- url     : https://prove2.me/theorems/01dd4f63-70e7-4c66-9514-5eb283e81794
-- title:
--   Stationary independent increments factor the expectation of exponential absolute partition sums
-- statement:
--   Factor exp of the negative finite sum into a finite product of exponentials of negative absolute increments. Apply the source independent-increments predicate on the monotone uniform grid and the pinned Mathlib iIndepFun.integral_prod_comp. Stationarity and start_zero identify each expectation with that of X at time 1/(n+1). The proof must use the canonical source process, not an auxiliary realization.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Function Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch02.levyUniformGridExponentialAbsoluteSumExpectationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    ∀ n : ℕ,
      (∫ ω, Real.exp (-(∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω -
           X ((i.val : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω|)) ∂P) =
        (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1) := by
  sorry
