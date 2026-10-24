-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_positive_separatedWeights
-- name    : OAI.PiExponent.exists_positive_separatedWeights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:12:13.787266+00:00
-- url     : https://prove2.me/theorems/b7c26e80-ef21-4639-93e4-034979681d51
-- title:
--   Positive weights can satisfy any finite prefix threshold rule
-- statement:
--   For any function assigning a natural threshold to each finite list, one can choose a positive length-\(m\) weight vector whose every coordinate exceeds the threshold determined by its preceding coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

open scoped BigOperators

theorem OAI.PiExponent.exists_positive_separatedWeights
    (m : ℕ) (S : List ℕ → ℕ) :
    ∃ w : Fin m → ℕ,
      (∀ i, 0 < w i) ∧ OAI.PiExponent.separatedWeights S w := by sorry
