-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
-- name    : Kyprianou.Ch02.prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T14:09:13.578239+00:00
-- url     : https://prove2.me/theorems/1affc01a-b893-45a0-b61d-c5907a5b904c
-- title:
--   Almost-sure convergence of simple mark integrals on any finite-intensity Poisson window
-- statement:
--   For any fixed measurable window R of finite Poisson reference intensity, each Poisson random measure restricted to R is almost surely integer-valued (Proved LevyStochCalc.Poisson.ae_isIntegerValued_restrict). Apply Proved Kyprianou.Ch02.integerValuedFiniteDiracV1 to get a finite Dirac representation and finite atom coefficients on that conull event. Apply Kyprianou.Ch02.finiteDiracMarkIntegralTendstoV1 (already ACCEPTED submission 97fbb113-d17b-46bd-8286-50e2419863f8) to transfer pointwise convergence of simple mark functions to signed marked Poisson integrals. This forms the core of Eq. 2.3 finite-simple approximation path.
-- source:
--   Kyprianou (2006) Eq. (2.3), finite-intensity Poisson random measure and measure theory.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => ∫ z in R, f n z.2 ∂(N.N ω))
        atTop (𝓝 (∫ z in R, z.2 ∂(N.N ω))) := by sorry
