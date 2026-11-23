-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegralSquareIntegrableV1
-- name    : Kyprianou.Ch02.prmFiniteRegionMarkedIntegralSquareIntegrableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:47:27.918719+00:00
-- url     : https://prove2.me/theorems/01907697-a538-4205-9a2f-75e9fc04a42d
-- title:
--   Quadratic moment of a finite-intensity marked Poisson integral
-- statement:
--   For a Poisson random measure of Levy intensity ν with finite mass on B, and square-integrable real marks, the square of the raw sum of marks in any finite time window is integrable under P. This is the marked second-moment Campbell estimate, to be proved by disjoint simple-function approximation and Poisson second moments.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9; canonical raw L2 target eb083600-ee0e-49df-bdb2-b935107049a4

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionMarkedIntegralSquareIntegrableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∀ t : ℝ≥0, Integrable
      (fun ω => (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) ^ 2) P := by sorry
