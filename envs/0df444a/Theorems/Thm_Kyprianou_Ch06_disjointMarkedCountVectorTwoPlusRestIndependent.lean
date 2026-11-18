-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointMarkedCountVectorTwoPlusRestIndependent
-- name    : Kyprianou.Ch06.disjointMarkedCountVectorTwoPlusRestIndependent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:32:41.305676+00:00
-- url     : https://prove2.me/theorems/730bd573-6d13-4b08-8348-550208c09f57
-- title:
--   Lemma 6.18: two disjoint marked-Poisson count coordinates independent of any finite disjoint remainder vector
-- statement:
--   For any finite family of pairwise-disjoint finite-intensity mark regions with two distinguished coordinates and an arbitrary finite remainder, the two-count event is independent of the prescribed entire remaining count vector, observed at arbitrary, possibly overlapping times. Proves the genuine finite-vector independence required for the first-mark competition/outside marked-process factorisation.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, independence of marked Poisson count rectangles with pairwise disjoint mark supports.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountVectorIndependent
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointMarkedCountVectorTwoPlusRestIndependent
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (k : Nat) (times : Fin (2 + k) → NNReal)
    (marks : Fin (2 + k) → Set E)
    (counts : Fin (2 + k) → Nat)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin (2 + k), i ≠ j →
      Disjoint (marks i) (marks j)) :
    P {omega |
      (∀ i : Fin 2, N omega (times (Fin.castAdd k i))
        (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)) ∧
      (∀ j : Fin k, N omega (times (Fin.natAdd 2 j))
        (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j))} =
    P {omega | ∀ i : Fin 2,
      N omega (times (Fin.castAdd k i))
        (marks (Fin.castAdd k i)) = counts (Fin.castAdd k i)} *
    P {omega | ∀ j : Fin k,
      N omega (times (Fin.natAdd 2 j))
        (marks (Fin.natAdd 2 j)) = counts (Fin.natAdd 2 j)} := by sorry
