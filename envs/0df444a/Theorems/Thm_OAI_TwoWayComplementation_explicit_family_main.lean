-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_explicit_family_main
-- name    : OAI.TwoWayComplementation.explicit_family_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:35.953294+00:00
-- url     : https://prove2.me/theorems/6d08f5ef-2594-4216-b1e8-8af326632b6f
-- statement:
--   The theorem states that for every natural number n ≥ 4, writing H = Fin(n−2) (natural-number subtraction), there is a read-only two-way nondeterministic finite automaton A with exactly n states (state type Fin n) whose input alphabet is the set of binary relations on H, such that three things hold. First, the language accepted by A equals the source language: the set of finite words of relations on H whose relational composition (the empty word giving the identity relation) is nonempty. Acceptance for these machines means some finite run, possibly of length zero, from the initial state on the left endmarker reaches an accepting state, with the head confined to the input between two distinct endmarkers and each transition choosing a next state and a move left, stay, or right. Second, for every finite-state-type Q and every such two-way automaton B over the same alphabet with state type Q whose language is exactly the complement of A's language, the cardinality of Q is at least (1/2)·2^⌊(n−4)/127⌋ − 1, where the exponent uses natural-number floor division. Third, if additionally n ≥ 131, then every deterministic such automaton D (at most one next-state and move pair for each state and scanned symbol) over any finite state type Q that accepts exactly A's language has at least (1/2)·2^⌊(n−4)/127⌋ states. Both lower bounds thus hold for the same n-state witness A. The statement is admitted in the source without a proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TwoWayDeterminization.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TwoWayDeterminization.lean; bytes 2264..2982
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Both lower bounds hold for the same n-state liveness witness. -/
theorem explicit_family_main (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) ∧
      (131 ≤ n → ∀ (Q : Type*) [Fintype Q],
        ∀ D : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        D.Deterministic → D.language = A.language →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ)) := by
  sorry

end TwoWayComplementation
end OAI
