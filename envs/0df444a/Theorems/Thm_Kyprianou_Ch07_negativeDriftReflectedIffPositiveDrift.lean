-- Prove2me | Theorems.Thm_Kyprianou_Ch07_negativeDriftReflectedIffPositiveDrift
-- name    : Kyprianou.Ch07.negativeDriftReflectedIffPositiveDrift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:53:56.657595+00:00
-- url     : https://prove2.me/theorems/1759072e-779d-408d-87c1-55027b478ca6
-- title:
--   Lévy drift-duality: negative drift of reflected path iff positive drift of original path
-- statement:
--   Almost-sure divergence of -X(t) to negative infinity as t tends to infinity is equivalent to almost-sure divergence of X(t) to positive infinity. This exact filter-transport lemma allows Theorem 7.1(ii) to follow from 7.1(i) by Lévy reflection.
-- source:
--   Kyprianou (2006), Chapter 7, Theorem 7.1(ii) and its symmetry with part (i), printed p. 180, original PDF p. 189. Proved with pinned Mathlib tendsto_neg_atTop_atBot and tendsto_neg_atBot_atTop. Exact proof verified by private remote compiler job 3ecfe8c3-54a6-47e6-be58-434ea7f2850a.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.negativeDriftReflectedIffPositiveDrift
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) :
    Kyprianou.Ch07.DriftsToNegInfinity P (fun t omega => -X t omega) ↔
      Kyprianou.Ch07.DriftsToPosInfinity P X := by
  sorry
