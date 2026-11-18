-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountAdditivityAe
-- name    : Kyprianou.Ch06.finiteDisjointMarkedCountAdditivityAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:11:28.199626+00:00
-- url     : https://prove2.me/theorems/318bc9ae-9a35-4992-b809-02de8ce3df43
-- title:
--   Lemma 6.18: finite additivity of marked-Poisson counts over disjoint measurable mark families
-- statement:
--   For any finite pairwise disjoint family of mark sets, the count N_t of their union equals the sum of their N_t counts, simultaneously for all observation times on an almost-sure event. Derives from the finite-additivity pathwise clause of IsMarkedPoissonPointProcess. This is the mark-atom summation step required to reconstruct overlapping outside-mark observations in Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite marked Poisson atom partition.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteDisjointMarkedCountAdditivityAe
    {Omega E ι : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    [DecidableEq ι]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (D : ι → Set E) (s : Finset ι)
    (hDisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j)) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t (⋃ i ∈ s, D i) = ∑ i ∈ s, N omega t (D i) := by sorry
