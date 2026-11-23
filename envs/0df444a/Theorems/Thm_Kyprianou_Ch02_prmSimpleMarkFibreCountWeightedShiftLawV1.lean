-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkFibreCountWeightedShiftLawV1
-- name    : Kyprianou.Ch02.prmSimpleMarkFibreCountWeightedShiftLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:28:24.990907+00:00
-- url     : https://prove2.me/theorems/4433c648-a08a-4520-81d5-572c02f4ee79
-- title:
--   Stationary law for finite-simple mark weighted Poisson fibre counts
-- statement:
--   A finite-simple mark f induces pairwise disjoint Borel mark fibres {y| f y=x}, indexed by its finite range. The weighted finite sum of Poisson counts of those fibres is measurable and has equal laws on shifted and unshifted windows. Transfer Proved Kyprianou.Ch02.prmFiniteSimpleMarkedSumStationaryAndMeasurableV1, indexed by Fin n, via Finset.equivFin f.range and Finset.sum_equiv. Use f.measurable and disjointness of fibres for distinct values. This is the source-exact finite-simple count law used in Eq 2.3 stationary-window proof.
-- source:
--   Kyprianou (2006) Ch.2 Eq.2.3, source-correct KLS PoissonRandomMeasure.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSimpleMarkFibreCountWeightedShiftLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (s t : ℝ≥0) :
    Measurable (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) ∧
    P.map (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) =
    P.map (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) := by sorry
