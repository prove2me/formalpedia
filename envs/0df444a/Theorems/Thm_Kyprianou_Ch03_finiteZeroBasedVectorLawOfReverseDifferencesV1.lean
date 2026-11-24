-- Prove2me | Theorems.Thm_Kyprianou_Ch03_finiteZeroBasedVectorLawOfReverseDifferencesV1
-- name    : Kyprianou.Ch03.finiteZeroBasedVectorLawOfReverseDifferencesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:22:51.688812+00:00
-- url     : https://prove2.me/theorems/fe7eafa0-0d49-4094-a931-57ec3bf6d298
-- title:
--   Zero-based finite vector law from reverse successive difference laws
-- statement:
--   The finite vector with zero first coordinate is reconstructed from reverse consecutive differences by negative prefix sums. The reconstruction is measurable. Apply it to the identical increment laws.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; parent rawReversalFiniteCylinderV1 8ac9ed28-eeeb-4802-8031-7ce3fe9b88b5.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.finiteZeroBasedVectorLawOfReverseDifferencesV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (n : Nat)
    (F G : Omega → Fin (n + 1) → Real)
    (hF : AEMeasurable F P) (hG : AEMeasurable G P)
    (hF0 : ∀ ω, F ω 0 = 0) (hG0 : ∀ ω, G ω 0 = 0)
    (hLaw : P.map (fun ω : Omega => fun i : Fin n =>
      F ω i.castSucc - F ω i.succ) =
      P.map (fun ω : Omega => fun i : Fin n =>
        G ω i.castSucc - G ω i.succ)) :
    P.map F = P.map G := by sorry
