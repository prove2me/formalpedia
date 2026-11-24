-- Prove2me | Theorems.Thm_Kyprianou_Ch02_canonicalMarginalSmallTimeDataV2
-- name    : Kyprianou.Ch02.canonicalMarginalSmallTimeDataV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:30.368816+00:00
-- url     : https://prove2.me/theorems/3230989e-f20e-439a-a00f-a8f62e803e99
-- title:
--   Canonical small-time data of the given probability-measure family
-- statement:
--   Apply the proved joint small-time extraction, variance correction and exponent identity. Form the extracted triplet and use the proved injectivity of the characteristic exponent to identify it with the prescribed triplet, retaining the convergence data and exact drift correction.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, via the Lévy–Khintchine small-time extraction and uniqueness.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.canonicalMarginalSmallTimeDataV2
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hT : ∀ t ξ, charFun (M t : Measure ℝ) ξ =
      Complex.exp (((t.val : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ)) :
    ∃ (r b_r : ℝ) (σ_sq_r : ℝ≥0) (ts : ℕ → {t : ℝ // 0 < t}),
      r ∈ Set.Ioc (1 / 2 : ℝ) 1 ∧
      T.levyMeasure {x | |x| = r} = 0 ∧
      Tendsto (fun n => (ts n).val) atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ∂(M (ts n) : Measure ℝ))
        atTop (nhds b_r) ∧
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(M (ts n) : Measure ℝ))
        atTop (nhds (σ_sq_r : ℝ)) ∧
      T.drift = b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂T.levyMeasure ∧
      (T.gaussianVariance : ℝ) =
        (σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂T.levyMeasure ∧
      ∀ f : BoundedContinuousFunction ℝ ℝ,
        (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
        Tendsto (fun n => (ts n).val⁻¹ *
          ∫ x, f x ∂(M (ts n) : Measure ℝ))
          atTop (nhds (∫ x, f x ∂T.levyMeasure)) := by
  sorry
