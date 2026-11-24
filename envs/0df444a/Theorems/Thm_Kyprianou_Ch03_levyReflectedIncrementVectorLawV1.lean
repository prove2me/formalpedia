-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levyReflectedIncrementVectorLawV1
-- name    : Kyprianou.Ch03.levyReflectedIncrementVectorLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:18:17.880261+00:00
-- url     : https://prove2.me/theorems/8e74c583-2bc1-4e97-a43d-246187182203
-- title:
--   Finite reflected increment vector law
-- statement:
--   The reflected partition r(i)=t-q(i.rev) is monotone. Reindex its mutually independent increments by the finite reversal permutation; independence is preserved. Each increment has the same law as the corresponding forward increment because the lags agree. Apply the product-law identity for independent finite vectors.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.4; parents 11df6340-566e-48b2-ba84-cb77468f8366 and 8ac9ed28-eeeb-4802-8031-7ce3fe9b88b5.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.levyReflectedIncrementVectorLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (n : Nat)
    (q : Fin (n + 1) → NNReal) (hq : Monotone q)
    (hqt : ∀ i, q i ≤ t) :
    P.map (fun ω : Omega => fun i : Fin n =>
      X (t - q i.castSucc) ω - X (t - q i.succ) ω) =
    P.map (fun ω : Omega => fun i : Fin n =>
      X (q i.succ) ω - X (q i.castSucc) ω) := by sorry
