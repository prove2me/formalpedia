-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictCompoundPoissonRealisation
-- name    : Kyprianou.Ch01.geometricStoppedWalkStrictCompoundPoissonRealisation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T07:17:26.863007+00:00
-- url     : https://prove2.me/theorems/a0ef49cd-7be6-4ecc-bdd5-5419dd767baf
-- title:
--   Genuine compound-Poisson realisation of an independent, strictly geometrically stopped IID sum
-- statement:
--   Under all the source hypotheses of Chapter 1 Exercise 1.2(ii) with 0<p<1, the stopped IID random sum has exactly the time-one law of a genuine compound-Poisson driver with positive rate and no zero mark mass. This is the substantive representation step, with all original independence and measurable-law conditions preserved.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii).

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedWalkStrictCompoundPoissonRealisation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω')
      (τ Y : ℕ → Ω' → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω) =
        μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ)) := by
  sorry
