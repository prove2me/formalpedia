-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyCanonicalFiniteVariationResidualModelV1
-- name    : Kyprianou.Ch02.levyCanonicalFiniteVariationResidualModelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:28:52.956662+00:00
-- url     : https://prove2.me/theorems/49f6d06b-51e6-4dce-9b81-02f44ae09450
-- title:
--   Canonical zero-Gaussian finite-first-moment model with actual signed jump residual
-- statement:
--   Construct the genuine pure-jump Levy model on a Poisson point family using finite first absolute small-mark moment. On a single conull event the small compensated annulus sums converge to the uncompensated absolutely summable chronological series minus their linear compensator. Large marks are locally finite. Identify the actual jumps of this path, yielding the signed residual for every horizon. The drift need not be specified in the statement.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; canonical finite first moment model and equality of real Levy path laws.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyCanonicalFiniteVariationResidualModelV1
    (a : ℝ) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) :
    ∃ (Λ : Type) (mΛ : MeasurableSpace Λ),
      letI : MeasurableSpace Λ := mΛ
      ∃ (Q : Measure Λ) (Y : ℝ≥0 → Λ → ℝ) (d : ℝ),
        IsProbabilityMeasure Q ∧ IsLevyProcess Y Q ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (Q.map (Y t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              Kyprianou.Ch01.levyTripleExponent
                ⟨-a, 0, levyMeasure, hlevyMeasure⟩ ξ)) ∧
        (∀ᵐ ω ∂Q, ∀ T : ℝ≥0,
          Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
            |Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|) ∧
          Y T ω = d * (T : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) T,
              (Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0))) := by
  sorry
