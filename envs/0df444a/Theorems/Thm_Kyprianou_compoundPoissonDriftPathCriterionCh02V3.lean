-- Prove2me | Theorems.Thm_Kyprianou_compoundPoissonDriftPathCriterionCh02V3
-- name    : Kyprianou.compoundPoissonDriftPathCriterionCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:29:28.589959+00:00
-- url     : https://prove2.me/theorems/16247fb4-6695-466f-b022-292129559cb6
-- title:
--   Lemma 2.13: compound-Poisson-with-drift path representation
-- statement:
--   A real Lévy process is a compound-Poisson process with drift if and only if its Gaussian coefficient is zero and the total Lévy jump intensity is finite. The process representation is explicit: either the jump measure is zero and X is deterministic linear drift, or X has the same Lévy finite-dimensional distributions as a compound-Poisson driver with drift d, positive rate r, jump law F, and actual jump measure rF. The previous theorem giving only the equivalent characteristic exponent remains a supporting bridge.
-- source:
--   Kyprianou (2006), Lemma 2.13 and formula (2.22), pp. 54-55

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem compoundPoissonDriftPathCriterionCh02V3
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
    ((∃ (d : ℝ),
      (levyMeasure = 0 ∧
       ∀ (t : ℝ≥0), ∀ᵐ ω ∂P, X t ω = d * (t : ℝ)) ∨
      (∃ (r : ℝ≥0) (hr : 0 < r)
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
                     LevyFoundations.compoundPoisson d τ Y (t : ℝ) ω))) ↔
     σ = 0 ∧ levyMeasure Set.univ < ⊤) := by sorry

end Kyprianou
