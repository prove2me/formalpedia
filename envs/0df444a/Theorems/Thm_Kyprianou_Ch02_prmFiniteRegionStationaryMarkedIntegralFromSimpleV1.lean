-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStationaryMarkedIntegralFromSimpleV1
-- name    : Kyprianou.Ch02.prmFiniteRegionStationaryMarkedIntegralFromSimpleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:00:05.731451+00:00
-- url     : https://prove2.me/theorems/c25d7325-63ab-4beb-b13e-a487df35428b
-- title:
--   Stationary law of full marked Poisson integrals from finite-simple marked sums
-- statement:
--   Genuine finite-simple approximation transfer theorem: given equality in law for every finite disjoint-cell weighted marked Poisson count sum on shifted versus initial time windows, show equality in law of the full real-valued marked Poisson integrals. The proof must construct deterministic finite-simple mark approximants converging almost surely under the KLS finite-intensity local atomic representation and transfer convergence in distribution. Integrability of the mark under ν is not assumed and must not be silently introduced; each bounded time window has finitely many marks almost surely.
-- source:
--   Kyprianou (2006) Chapter 2 finite-activity Lévy component and the KLS PRM finite atomic support. Direct needed child of the stationary marginal marked-integral law.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionStationaryMarkedIntegralFromSimpleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hSimple : ∀ (n : ℕ) (C : Fin n → Set ℝ)
      (hC : ∀ i, MeasurableSet (C i))
      (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
      (w : Fin n → ℝ) (s t : ℝ≥0),
      P.map (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ (B ∩ C i))).toReal) =
      P.map (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal)) :
    ∀ s t : ℝ≥0,
      P.map (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) =
      P.map (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) := by sorry
