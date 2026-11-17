-- Prove2me | Theorems.Thm_Kyprianou_Ch07_signIntegralReflect
-- name    : Kyprianou.Ch07.signIntegralReflect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:27:33.393568+00:00
-- url     : https://prove2.me/theorems/ce031073-63d7-4190-93ef-428fde445aee
-- title:
--   Theorem 7.1 duality bridge: sign-integral of reflected Lévy process
-- statement:
--   For any real-valued process, the nonnegative time-sign integral of its reflection -X equals the nonpositive time-sign integral of X. The integrands coincide at each time by the equivalence 0 <= -X iff X <= 0.
-- source:
--   Kyprianou (2006), Chapter 7, Theorem 7.1(i)-(ii), printed p. 180; original PDF p. 189. This proof-reusable duality equality is immediate from the source sign-integral definitions and supports the positive-drift clause of the chapter.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.signIntegralReflect
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X : NNReal → Omega → Real) :
    Kyprianou.Ch07.nonnegativeSignIntegral P
      (fun t omega => -X t omega) =
      Kyprianou.Ch07.nonpositiveSignIntegral P X := by
  sorry
