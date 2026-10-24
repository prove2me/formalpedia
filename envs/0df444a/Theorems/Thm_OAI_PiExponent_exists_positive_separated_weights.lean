-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_positive_separated_weights
-- name    : OAI.PiExponent.exists_positive_separated_weights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:13:01.46109+00:00
-- url     : https://prove2.me/theorems/5ac6e37c-706b-4bd4-a8cd-cd211068b8a7
-- title:
--   Positive weights satisfying finite recursive separation thresholds
-- statement:
--   For any threshold function on finite lists and any positive length, there is a positive weight vector meeting the threshold at each index using the earlier weights as its prefix.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

theorem OAI.PiExponent.exists_positive_separated_weights
    (S : List ℕ → ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ w : Fin m → ℕ, (∀ i, 0 < w i) ∧ OAI.PiExponent.separatedWeights S w := by sorry
