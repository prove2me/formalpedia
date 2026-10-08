-- Prove2me | Theorems.Thm_OAI_ThreeState_regular_supercritical
-- name    : OAI.ThreeState.regular_supercritical
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:31.852357+00:00
-- url     : https://prove2.me/theorems/d5ea19bd-1ef2-4c7d-a4c1-c415f6393d50
-- statement:
--   The theorem states that, for every natural number b ≥ 2 and every real λ that is admissible, meaning −1/2 ≤ λ ≤ 1, if b·λ² > 1 then the sequence of regular-tree advantages reconstructs. Here a three-state spin (an element of Fin 3) is passed through a symmetric channel that keeps the spin with probability (1+2λ)/3 and moves to each other spin with probability (1−λ)/3. The observation at depth 0 is the root spin, and the observation at depth n+1 is a multiset of depth-n observations, one for each of the offspring of the root, where the offspring count is the constant b (the regular case) and each child spin is obtained by passing the parent spin through the channel and then observed recursively. With a uniformly random root spin, the posterior of each spin given an observation is its conditional probability, defaulting to 1/3 when the observation has probability zero. The advantage of a family of laws indexed by the root spin is the sum over observations y of the marginal probability of y times half the sum over spins i of |posterior(y,i) − 1/3|. The regular advantage at depth n is this advantage for the regular b-ary observation law. Reconstructs means that this sequence in n converges to some limit L > 0. The statement is an admitted theorem, with its proof left as sorry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeStateSupercritical.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeStateSupercritical.lean; bytes 3197..3378
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ThreeStateSupercritical

namespace OAI

namespace ThreeState

theorem regular_supercritical (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < (b : ℝ) * lam ^ 2) : Reconstructs (regularAdvantage b lam h) := by
  sorry

end ThreeState
end OAI
