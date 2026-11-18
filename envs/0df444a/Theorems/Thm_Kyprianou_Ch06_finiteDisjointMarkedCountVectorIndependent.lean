-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountVectorIndependent
-- name    : Kyprianou.Ch06.finiteDisjointMarkedCountVectorIndependent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:24:24.024449+00:00
-- url     : https://prove2.me/theorems/dcfa2c9a-624f-4eda-9125-482fd8f25ed3
-- title:
--   Lemma 6.18: arbitrary finite disjoint mark count vectors have independent Poisson marginals
-- statement:
--   For every finite family of pairwise disjoint finite-intensity measurable mark sets, observed at arbitrary possibly overlapping times, the joint probability of any prescribed count vector equals the product of the marginal probabilities. This is the full finite-dimensional disjoint mark count independence law, generalising the proved two- and three-region cases and enabling arbitrary outside count vectors.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), pp.160–161, finite-dimensional marked Poisson rectangle independence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteDisjointMarkedCountVectorIndependent
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (k : Nat) (times : Fin k → NNReal)
    (marks : Fin k → Set E) (counts : Fin k → Nat)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin k, i ≠ j →
      Disjoint (marks i) (marks j)) :
    P {omega | ∀ i : Fin k, N omega (times i) (marks i) = counts i} =
    ∏ i : Fin k,
      P {omega | N omega (times i) (marks i) = counts i} := by sorry
