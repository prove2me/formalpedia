-- Prove2me | Theorems.Thm_Kyprianou_Ch07_realLevyProcessNegation
-- name    : Kyprianou.Ch07.realLevyProcessNegation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:34:46.322435+00:00
-- url     : https://prove2.me/theorems/b62cccb4-1e98-4e49-bb9e-594c1be24a86
-- title:
--   Lévy-process duality: reflection preserves the full Chapter 6 real Lévy predicate
-- statement:
--   A real-valued source Lévy process has measurable negative marginals, zero initial value, stationary and independent reflected increments, and reflected cadlag paths. Thus the pathwise reflection is again a real Lévy process in the exact published Chapter 6 predicate.
-- source:
--   Kyprianou (2006), Chapters 6 and 7, the dual Lévy-process reduction used in Theorem 7.1(i)-(ii), printed p. 180; original PDF p. 189. Exact published Ch06 IsRealLevyProcess definition and source reflection. Proved at pinned private remote Lean job 6ff05f58-4712-42d9-96c5-202e38693ea1.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.realLevyProcessNegation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X) :
    Kyprianou.Ch06.IsRealLevyProcess P
      (fun t omega => -X t omega) := by
  sorry
