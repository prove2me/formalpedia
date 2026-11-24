-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfFiniteVectorPairTransferV1
-- name    : Kyprianou.Ch03.supInfFiniteVectorPairTransferV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T10:08:40.961026+00:00
-- url     : https://prove2.me/theorems/f43702ec-6212-4a29-87c1-33ed9a25242a
-- title:
--   Extrema pair transfer for finite reflected vector laws
-- statement:
--   Push the vector law through the measurable map v ↦ (sup v, sup v-v(last)). Reversal permutes the finite range; the supremum of c-v is c-inf v, and the reflected last coordinate is c since v(0)=0.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; dyadic and limit children of f3decb5b-3c0d-4063-b885-79044b1ecb2f.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfFiniteVectorPairTransferV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (m : ℕ) (V : Omega → Fin (m + 1) → Real)
    (hV : AEMeasurable V P) (hV0 : ∀ ω, V ω 0 = 0)
    (hLaw : P.map V = P.map (fun ω : Omega => fun i =>
      V ω (Fin.last m) - V ω i.rev)) :
    P.map (fun ω : Omega =>
      let a := sSup (Set.range (V ω))
      (a, a - V ω (Fin.last m))) =
    P.map (fun ω : Omega =>
      let b := sInf (Set.range (V ω))
      (V ω (Fin.last m) - b, -b)) := by sorry
