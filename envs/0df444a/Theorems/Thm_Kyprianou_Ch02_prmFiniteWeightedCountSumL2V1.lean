-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteWeightedCountSumL2V1
-- name    : Kyprianou.Ch02.prmFiniteWeightedCountSumL2V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:57:21.475172+00:00
-- url     : https://prove2.me/theorems/0e8d1144-1aa8-458d-a719-ad3076ae2ef1
-- title:
--   Square-integrability of finite weighted sums of KLS Poisson counts
-- statement:
--   Every finite weighted sum of evaluations of a Poisson random measure on finite-intensity measurable regions is square integrable, regardless of overlaps. Follows from square integrability of each finite-intensity count and closure of L2 under scalar multiplication and finite sums. Gives the discrete/simple mark component of the Chapter 2 marked-Poisson quadratic approximation.
-- source:
--   Kyprianou (2006), Chapter 2 Poisson random measure finite-simple integral moments; KLS compensated square-integrability

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteWeightedCountSumL2V1
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (F : Finset ι) (C : ι → Set (ℝ × ℝ))
    (hC : ∀ i ∈ F, MeasurableSet (C i))
    (hfinite : ∀ i ∈ F, LevyStochCalc.Poisson.referenceIntensity ν (C i) ≠ ⊤)
    (a : ι → ℝ) :
    MemLp (fun ω => ∑ i ∈ F, a i * (N.N ω (C i)).toReal) 2 P := by sorry
