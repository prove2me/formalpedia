-- Prove2me | Theorems.Thm_OAI_PiExponent_separatedWeights_snoc
-- name    : OAI.PiExponent.separatedWeights_snoc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:06:15.774013+00:00
-- url     : https://prove2.me/theorems/c58b14eb-d5f9-4898-8b39-d9a898120b61
-- title:
--   Successive weight condition under appending a final weight
-- statement:
--   A tuple formed by appending one final weight satisfies all successive thresholds exactly when its original prefix does and the threshold applied to the full original weight list is at most the appended weight. This includes the empty tuple case, where the original condition is vacuous and the new threshold uses the empty list.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

theorem OAI.PiExponent.separatedWeights_snoc
    (S : List ℕ → ℕ) {m : ℕ} (w : Fin m → ℕ) (x : ℕ) :
    OAI.PiExponent.separatedWeights S (Fin.snoc w x) ↔
      OAI.PiExponent.separatedWeights S w ∧ S (List.ofFn w) ≤ x := by sorry
