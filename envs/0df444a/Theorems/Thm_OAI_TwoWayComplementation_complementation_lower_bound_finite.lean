-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_complementation_lower_bound_finite
-- name    : OAI.TwoWayComplementation.complementation_lower_bound_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:35.724315+00:00
-- url     : https://prove2.me/theorems/71d04e96-02f4-442d-a9c3-de535288a73f
-- statement:
--   The theorem states that for every natural number n ≥ 4 there is a two-way nondeterministic finite automaton A with n states whose input alphabet is the set of binary relations on {0,…,n−3} (subsets of Fin(n−2) × Fin(n−2)), such that the following lower bound holds. Here a two-way automaton has an initial state, a set of accepting states, and a transition map sending a state and the scanned tape symbol (a left endmarker, a right endmarker, or an input letter) to a set of pairs (new state, move), where the move is left, stay or right; the input word sits between the two endmarkers, the head starts on the left endmarker in the initial state, and a word is accepted if some finite sequence of steps reaches an accepting state. For every finite state type Q and every two-way nondeterministic automaton B over the same alphabet with state set Q, if the language of B is exactly the complement of the language of A, then the number of states of B satisfies |Q| ≥ (1/2)·2^⌊(n−4)/127⌋ − 1, where the exponent (n−4)/127 is read as natural-number division, so n−4 is truncated subtraction and the quotient is rounded down. Thus complementing A requires exponentially many states in n/127 for two-way nondeterministic automata.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TwoWayComplementation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TwoWayComplementation.lean; bytes 1061..1415
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TwoWayComplementation

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem complementation_lower_bound_finite (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      ∀ (Q : Type*) [Fintype Q], ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ) := by
  sorry

end TwoWayComplementation
end OAI
