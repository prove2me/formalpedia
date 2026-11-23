-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteSimpleMarkedSumStationaryAndMeasurableV1
-- name    : Kyprianou.Ch02.prmKLSFiniteSimpleMarkedSumStationaryAndMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:11:26.329879+00:00
-- url     : https://prove2.me/theorems/8820d6ee-c1fb-4230-80af-e75557fc86e6
-- title:
--   Finite weighted Poisson count sums are measurable and shift stationary for KLS provider
-- statement:
--   Exact adaptation of proved Kyprianou.Ch02.prmFiniteSimpleMarkedSumStationaryAndMeasurableV1, but using Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure and KLS vector-count theorem. No importing F000 provider. Links directly to simple-mark-fibre count law and Eq 2.3.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3); KLS-modular PoissonRandomMeasure provider.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmKLSFiniteSimpleMarkedSumStationaryAndMeasurableV1
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
          (N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ (B ∩ C i))).toReal) =
      P.map (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) := by sorry
