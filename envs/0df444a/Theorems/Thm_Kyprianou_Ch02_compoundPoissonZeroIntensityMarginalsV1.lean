-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compoundPoissonZeroIntensityMarginalsV1
-- name    : Kyprianou.Ch02.compoundPoissonZeroIntensityMarginalsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:31:42.817192+00:00
-- url     : https://prove2.me/theorems/87ecc3f5-bc26-46bf-83d6-ed604a56e84a
-- title:
--   Zero Gaussian variance and zero jump intensity imply deterministic drift marginals
-- statement:
--   The zero jump measure and zero Gaussian variance leave the linear drift exponent. Identify the marginal with the point mass at -a*t by characteristic function uniqueness, then recover the almost-sure value from its pushforward law.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.13; finite-activity Lévy process criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.compoundPoissonZeroIntensityMarginalsV1
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
    σ = 0 → levyMeasure = 0 →
    (∀ (t : ℝ≥0), ∀ᵐ ω ∂P, X t ω = (-a) * (t : ℝ)) := by
  sorry
