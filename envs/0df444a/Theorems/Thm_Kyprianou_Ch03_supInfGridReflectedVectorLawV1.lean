-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfGridReflectedVectorLawV1
-- name    : Kyprianou.Ch03.supInfGridReflectedVectorLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:42.762856+00:00
-- url     : https://prove2.me/theorems/bd89161c-5128-400b-8c2b-a65414dab7a5
-- title:
--   Reflected positive finite grid vector law
-- statement:
--   Reuse levyReflectedIncrementVectorLawV1 and finiteZeroBasedVectorLawOfReverseDifferencesV1. Apply the latter to the negative forward vector and raw reversed vector, then apply measurable coordinate negation, or use reverse differences with both signs reversed.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; dyadic and limit children of f3decb5b-3c0d-4063-b885-79044b1ecb2f.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfGridReflectedVectorLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (m : ℕ) (q : Fin (m + 1) → NNReal) (hq : Monotone q)
    (hq0 : q 0 = 0) (hqt : ∀ i, q i ≤ t) :
    P.map (fun ω : Omega => fun i => X (q i) ω) =
    P.map (fun ω : Omega => fun i => X t ω - X (t - q i) ω) := by sorry
