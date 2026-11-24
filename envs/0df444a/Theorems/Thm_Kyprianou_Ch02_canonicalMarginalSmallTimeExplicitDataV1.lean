-- Prove2me | Theorems.Thm_Kyprianou_Ch02_canonicalMarginalSmallTimeExplicitDataV1
-- name    : Kyprianou.Ch02.canonicalMarginalSmallTimeExplicitDataV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:59:16.931085+00:00
-- url     : https://prove2.me/theorems/e097fd43-a027-4336-89f8-37060111dc32
-- title:
--   Canonical small-time data for an explicit Lévy characteristic exponent
-- statement:
--   Identify the canonical small-time data of a marginal family given the explicit Lévy–Khintchine characteristic exponent. Use narrow imports to keep the legacy LeanLevy characteristic-function definitions separate from the Mathlib umbrella.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, via the Lévy–Khintchine small-time extraction and uniqueness.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.canonicalMarginalSmallTimeExplicitDataV1
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hT : ∀ t ξ, charFun (M t : Measure ℝ) ξ =
      Complex.exp (((t.val : ℝ) : ℂ) * (Complex.I * ((T.drift * ξ : ℝ) : ℂ) - (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) + ∫ y, ProbabilityTheory.levyCompensatedIntegrand ξ y ∂T.levyMeasure))) :
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
