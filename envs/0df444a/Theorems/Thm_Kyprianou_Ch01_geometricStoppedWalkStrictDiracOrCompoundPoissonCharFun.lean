-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictDiracOrCompoundPoissonCharFun
-- name    : Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:24:24.358085+00:00
-- url     : https://prove2.me/theorems/1fb66778-3f13-48db-bf08-f5a76f37956b
-- title:
--   Strict geometric stopped IID sum has Dirac-zero or genuine CP characteristic function
-- statement:
--   Under the exact source IID and independent geometric stopping assumptions, either the stopped sum has the Dirac-zero characteristic function, or a positive-rate compound-Poisson driver with nonzero jumps has the same characteristic function at every real frequency. This is the distributional Fourier identification needed for Chapter 1 Exercise 1.2(ii), including the degenerate all-zero-increments case.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), conditional Fourier series and logarithmic cluster representation.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonCharFun
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
    (∀ xi : ℝ,
      charFun (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
      charFun (Measure.dirac (0 : ℝ)) xi) ∨
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω')
      (τ Y : ℕ → Ω' → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      (∀ xi : ℝ,
        charFun (P.map (fun ω =>
          ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
        charFun (μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ))) xi) := by
  sorry
