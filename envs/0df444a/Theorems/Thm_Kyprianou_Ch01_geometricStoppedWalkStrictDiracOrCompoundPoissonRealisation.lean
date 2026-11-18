-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictDiracOrCompoundPoissonRealisation
-- name    : Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonRealisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:19:33.273204+00:00
-- url     : https://prove2.me/theorems/9be7952b-79ba-40db-ac47-9e406a999cb6
-- title:
--   Strict geometric IID stopped sum: Dirac zero or genuine compound-Poisson marginal
-- statement:
--   For any strictly geometric independent stopping count and IID real increments, the random-sum law is either Dirac zero or exactly a time-one compound-Poisson marginal with positive rate and jump distribution supported away from zero. The degenerate all-zero increment case is explicitly allowed. Every source measurability and independence hypothesis is preserved.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii); compound-geometric infinite-divisibility representation with degenerate case included.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonRealisation
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
    (P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω) =
      Measure.dirac (0 : ℝ)) ∨
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
