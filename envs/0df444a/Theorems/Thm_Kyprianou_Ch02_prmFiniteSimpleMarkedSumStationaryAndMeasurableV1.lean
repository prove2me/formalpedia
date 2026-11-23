-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkedSumStationaryAndMeasurableV1
-- name    : Kyprianou.Ch02.prmFiniteSimpleMarkedSumStationaryAndMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:59:17.966796+00:00
-- url     : https://prove2.me/theorems/14b46ecd-a1cf-4f68-a449-96befd6f1541
-- title:
--   Finite-simple Poisson marked-sum measurability and time-stationarity
-- statement:
--   For a finite mark region B and any finite measurable pairwise-disjoint mark-cell partition, the finite weighted marked sum over the initial time window is measurable; its entire distribution is invariant under shifting the time window. The two conclusions use already remotely Proved marked-window weighted count measurability and the finite vector shifted Poisson count law. This is the exact finite-simple stationary marked-integral approximation step in the Lévy process proof, without any unjustified point-family representation.
-- source:
--   Kyprianou Chapter 2, simple-mark finite-activity compound-Poisson approximation; source-exact KLS PRM fields.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleMarkedSumStationaryAndMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (w : Fin n → ℝ) (s t : ℝ≥0) :
    Measurable (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) ∧
    P.map (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ (B ∩ C i))).toReal) = P.map (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) := by sorry
