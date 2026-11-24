-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDuality_uniformGridGeometry
-- name    : Kyprianou.Ch03.supInfDuality_uniformGridGeometry
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:16.572846+00:00
-- url     : https://prove2.me/theorems/72412414-5c16-4fee-a6e5-770dfff2cdab
-- title:
--   Uniform grid endpoints, order and reflection
-- statement:
--   The equally spaced grid is monotone, contains zero and the horizon, and is invariant under reflection in the horizon.
-- source:
--   Kyprianou (2006), Lemma 3.5; uniform-grid reversal proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDuality_uniformGridGeometry
    (m : ℕ) (hm : 0 < m) (t : NNReal) :
    let q : Fin (m + 1) → NNReal :=
      fun i => (i.val : NNReal) * (t / (m : NNReal))
    Monotone q ∧ q 0 = 0 ∧ q (Fin.last m) = t ∧
      (∀ i, q i ≤ t) ∧
      Set.range (fun i => t - q i) = Set.range q := by sorry
