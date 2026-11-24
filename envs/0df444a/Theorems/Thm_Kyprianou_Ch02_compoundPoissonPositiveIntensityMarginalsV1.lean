-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compoundPoissonPositiveIntensityMarginalsV1
-- name    : Kyprianou.Ch02.compoundPoissonPositiveIntensityMarginalsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:31:47.895651+00:00
-- url     : https://prove2.me/theorems/948118c6-cf90-4112-a348-df8b7651a58c
-- title:
--   Positive finite jump intensity and zero Gaussian variance give compound Poisson drift marginals
-- statement:
--   Normalise the finite Lévy measure into a probability mark law and construct the existing compound Poisson driver. Choose d = -a minus the small jump compensation integral. The compound Poisson triplet formula and uniqueness of characteristic functions identify every marginal.
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

theorem Kyprianou.Ch02.compoundPoissonPositiveIntensityMarginalsV1
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
    σ = 0 → levyMeasure Set.univ < ⊤ → 0 < levyMeasure Set.univ →
    (∃ (d : ℝ), (∃ (r : ℝ≥0) (hr : 0 < r)
         (F : Measure ℝ) (hF : IsProbabilityMeasure F),
         letI : IsProbabilityMeasure F := hF
         levyMeasure = (r : ENNReal) • F ∧
         ∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
           letI : MeasurableSpace Ω' := measΩ'
           ∃ (P' : Measure Ω') (hP' : IsProbabilityMeasure P'),
             letI : IsProbabilityMeasure P' := hP'
             ∃ (τ Y : ℕ → Ω' → ℝ),
               LevyFoundations.IsCompoundPoissonDriver τ Y r F P' ∧
               ∀ (t : ℝ≥0),
                 P.map (X t) =
                   P'.map (fun ω =>
                     LevyFoundations.compoundPoisson d τ Y (t : ℝ) ω))) := by
  sorry
