-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_main_theorem
-- name    : OAI.OneWayLiveness.main_theorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.466934+00:00
-- url     : https://prove2.me/theorems/c489910a-b34a-444c-a7ab-5af36d80d38a
-- statement:
--   The theorem states that for every natural number h ≥ 2 two things hold. First, there is a nondeterministic two-way finite automaton with h+3 states over the alphabet of binary relations on {0,…,h−1}, which never makes a left move (no transition of any state on any symbol moves left), and which recognizes the language OWL(h) under both acceptance conventions. Here OWL(h) is the set of words of relations whose ordered relational composition, taken in the monoid of relations with composition as product and equality as identity, is nonempty, that is, some x is related to some y by the product. The machine runs on the word framed by a left and a right endmarker, starts at the left endmarker in its initial state, and accepts a word if some finite run reaches an accepting state; in the positive convention the run must have at least one step, while in the other convention a zero-length run is allowed. Second, for every acceptance convention, every number s of states, and every deterministic two-way automaton with s states over the same alphabet that recognizes OWL(h) in that convention, the inequality 2^⌊(h−2)/31⌋ ≤ 4(s+2)^2 holds in the positive convention, and 2^⌊(h−2)/31⌋ ≤ 4(s+1)^2 holds in the other, with natural-number floor division in the exponent. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OneWayLiveness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OneWayLiveness.lean; bytes 3802..4160
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_OneWayLiveness

namespace OAI

namespace OneWayLiveness

theorem main_theorem (h : ℕ) (hh : 2 ≤ h) :
    (∃ N : NMachine (Alphabet h) (h + 3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (OWL h)) ∧
    (∀ (positive : Bool) (s : ℕ) (D : DMachine (Alphabet h) s),
      D.Recognizes positive (OWL h) →
      2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2) := by
  sorry

end OneWayLiveness
end OAI
