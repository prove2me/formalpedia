-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionShiftedSimpleApproxLawV1
-- name    : Kyprianou.Ch02.prmFiniteRegionShiftedSimpleApproxLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:42:11.593803+00:00
-- url     : https://prove2.me/theorems/cd0c85a8-2183-40da-94fc-4c181c840ba6
-- title:
--   Common simple marked Poisson integral approximants preserve shift law and converge a.s.
-- statement:
--   For a finite-intensity measurable mark region B, construct from ONE deterministic finite-simple approximation of the real mark function z↦z a sequence of measurable shifted-window and origin-window PRM integrals. The two approximants at each n have identical probability laws using the already Proved Kyprianou.Ch02.prmFiniteSimpleMarkedSumStationaryAndMeasurableV1. They converge almost surely to the full signed marked integrals, since on every bounded time window the random measure has only finitely many atoms almost surely and each simple approximation converges pointwise at every atom. Use source-correct KLS random measure interface, finite-window Dirac law and StronglyMeasurable.approx; do not assume a finite first moment ν.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3), finite-activity signed Poisson marked jump process.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionShiftedSimpleApproxLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ s t : ℝ≥0, ∃ F G : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Measurable (G n)) ∧
      (∀ n, P.map (F n) = P.map (G n)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop
        (𝓝 (∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop
        (𝓝 (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)))) := by sorry
