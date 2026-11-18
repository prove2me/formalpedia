-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonRectangleAxiomNormalisesProbability
-- name    : Kyprianou.Ch06.markedPoissonRectangleAxiomNormalisesProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:17:19.750226+00:00
-- url     : https://prove2.me/theorems/cbd27736-0bb7-4d77-917e-9f3cc29de7b4
-- title:
--   Marked Poisson rectangle axiom implies that the underlying measure has total mass one
-- statement:
--   Any measure satisfying the full marked Poisson finite-dimensional rectangle count axiom has total mass one. The empty family of count constraints is the whole sample space and the corresponding empty product of Poisson probabilities is one. This makes the probability-measure assumption available internally for marked-Poisson continuity arguments.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, marked Poisson point process definition and finite-dimensional count laws, k=0.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonRectangleAxiomNormalisesProbability
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    P Set.univ = 1 := by sorry
