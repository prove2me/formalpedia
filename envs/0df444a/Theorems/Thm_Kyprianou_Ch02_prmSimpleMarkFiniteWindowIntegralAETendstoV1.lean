-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkFiniteWindowIntegralAETendstoV1
-- name    : Kyprianou.Ch02.prmSimpleMarkFiniteWindowIntegralAETendstoV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:53:05.419798+00:00
-- url     : https://prove2.me/theorems/df4af996-de0c-42a0-9faa-3f0e5ef31572
-- title:
--   Pointwise finite-simple mark approximation converges to signed marked Poisson integral a.s.
-- statement:
--   Any deterministic sequence of real simple mark functions converging at every real mark to the identity gives a.s. convergence of its marked Poisson window integrals, for each fixed shifted and origin time window. Use the proved finite-window Dirac representation for the finite-activity Poisson random measure and tendsto_finset_sum for pointwise convergence over finitely many atoms. This avoids assuming a finite first moment of the Levy intensity. Essential child in Eq. (2.3) stationarity proof.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3); Mathlib finite-sum convergence plus finite support of PRM.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSimpleMarkFiniteWindowIntegralAETendstoV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x))
    (s t : ℝ≥0) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => ∫ z in
        (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
        f n z.2 ∂(N.N ω)) atTop
        (𝓝 (∫ z in
          (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
          z.2 ∂(N.N ω))) ∧
      Tendsto (fun n => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f n z.2 ∂(N.N ω)) atTop
        (𝓝 (∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω))) := by sorry
