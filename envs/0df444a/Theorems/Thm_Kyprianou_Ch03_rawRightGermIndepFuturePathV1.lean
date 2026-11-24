-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawRightGermIndepFuturePathV1
-- name    : Kyprianou.Ch03.rawRightGermIndepFuturePathV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:24:59.740933+00:00
-- url     : https://prove2.me/theorems/187ee402-4a86-494d-b6e1-72f4be49e0e0
-- title:
--   Raw Lévy right germ is independent of the entire future increment path
-- statement:
--   The raw right germ of a Lévy process is independent of the full shifted future path at t, in the sense of independence of sigma-algebras for P (which uses outer measures on null-measurable events). Pass to the ambient completion using the proved almost-everywhere path measurability. For a finite collection of future times, shift the origin to s decreasing to t, with s below all positive future times. At each s the joint future increments are independent of the raw past through s by finite partition independent increments. Apply a.e. right continuity and bounded continuous vector tests, then finite-cylinder extension. Zero-time increments are deterministic.
-- source:
--   Kyprianou (2006), Exercise 3.1; parent dc6deda8-897b-4e0f-b4f3-f2428ced614a.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.rawRightGermIndepFuturePathV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real) (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) :
    Indep (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) (MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X (t + u) ω - X t ω) inferInstance) P := by
  sorry
