-- Prove2me | Theorems.Thm_Kyprianou_Ch06_outsideMarkBooleanCountFamily
-- name    : Kyprianou.Ch06.outsideMarkBooleanCountFamily
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:28:19.747268+00:00
-- url     : https://prove2.me/theorems/fc6cad68-473a-4b7c-bad8-61a7ae6a6fde
-- title:
--   Lemma 6.18: simultaneous Poisson count expansion over finitely enumerated outside-mark atoms
-- statement:
--   For every finite family of overlapping finite-intensity outside-A mark sets, choose a deterministic finite family of pairwise disjoint measurable finite-intensity mark atoms. On a single almost-sure event, all original N_t(B_i) count values simultaneously equal sums over their selected atoms at every t. This is the complete spatial marked-Poisson component of Lemma 6.18(ii), independent of time-grid decomposition.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite overlapping mark count disjointisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_outsideBooleanAtomFiniteEnumeration
import Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountAdditivityAe
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.outsideMarkBooleanCountFamily
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) :
    ∃ (a : Nat) (mark : Fin a → Set E)
      (selected : Fin m → Finset (Fin a)),
      (∀ j, MeasurableSet (mark j) ∧ n (mark j) < ⊤ ∧
        Disjoint A (mark j)) ∧
      (∀ j l : Fin a, j ≠ l → Disjoint (mark j) (mark l)) ∧
      (∀ᵐ omega ∂P, ∀ i : Fin m, ∀ t : NNReal,
        N omega t (B i) =
          ∑ j ∈ selected i, N omega t (mark j)) := by sorry
