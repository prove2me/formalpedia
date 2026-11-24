-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDuality_orderedVectorLaw
-- name    : Kyprianou.Ch03.supInfDuality_orderedVectorLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:17.228949+00:00
-- url     : https://prove2.me/theorems/45b55b4b-0f5e-41d1-a89a-2b1f3622bd63
-- title:
--   Shifted reversal law on a finite ordered grid
-- statement:
--   Finite ordered time-grid reflected increment equality implies equality of the two zero-based cumulative vectors.
-- source:
--   Kyprianou (2006), Lemma 3.5; uniform-grid reversal proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDuality_orderedVectorLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (t : NNReal) (m : ℕ) (q : Fin (m + 1) → NNReal)
    (hq : Monotone q) (h0 : q 0 = 0) (hqt : ∀ i, q i ≤ t) :
    P.map (fun ω : Omega => fun i => X (t - q i) ω - X t ω) =
    P.map (fun ω : Omega => fun i => -X (q i) ω) := by sorry
