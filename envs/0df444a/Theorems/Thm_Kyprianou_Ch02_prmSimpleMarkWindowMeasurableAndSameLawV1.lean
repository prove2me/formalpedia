-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkWindowMeasurableAndSameLawV1
-- name    : Kyprianou.Ch02.prmSimpleMarkWindowMeasurableAndSameLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:53:02.159176+00:00
-- url     : https://prove2.me/theorems/b51d11db-8cbf-4d4e-b699-9e01536c9363
-- title:
--   Finite-simple marked Poisson window integrals are measurable and time-stationary
-- statement:
--   For any real-valued measurable simple function of the mark, integrals over a finite-intensity B in shifted/original windows are measurable and have equal laws. Show the integral of finite-simple marks equals a weighted sum of counts over disjoint mark fibres (modulo the conull finite-count event). Apply already proved Kyprianou.Ch02.prmFiniteSimpleMarkedSumStationaryAndMeasurableV1. This is a concrete child of the accepted stationary-window Eq. (2.3) branch.
-- source:
--   Kyprianou (2006) Chapter 2 Poisson random measure Eq. (2.3), finite simple mark functions.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSimpleMarkWindowMeasurableAndSameLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (s t : ℝ≥0) :
    Measurable (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) ∧
    Measurable (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) ∧
    P.map (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) =
    P.map (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) := by sorry
