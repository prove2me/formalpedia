-- Prove2me | Theorems.Thm_OAI_SnakyPrototype_snaky_winning_strategy_21_with_legal_states
-- name    : OAI.SnakyPrototype.snaky_winning_strategy_21_with_legal_states
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:23.838799+00:00
-- url     : https://prove2.me/theorems/29b16242-e6c3-4ee3-b459-3e4a883b9dcc
-- statement:
--   The theorem states that there is a policy σ for a Maker–Breaker-style placement game on the integer grid ℤ×ℤ, where a policy maps the number r of remaining rounds, the finite set M of cells already claimed by the maker, and the finite set B of cells already claimed by the blocker to a cell, such that σ always proposes a cell lying in neither M nor B, and such that for every blocker reply sequence β : ℕ → ℤ×ℤ that is legal before the final round, the following hold. Play starts from empty sets; at round k (counting from 0) with N = 21, the maker adds σ(21−k, M, B) to M and the blocker adds β(k) to B. Legality means that for every k with k+1 < 21, β(k) is not already in the maker's set, not the maker's cell chosen in that same round, and not already in the blocker's set. Under this legality assumption, the maker's set after 21 rounds contains a copy of the six-cell shape snaky = {(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}, placed by one of the eight rotations or reflections of the grid (as given by the orient map) followed by a translation. That final maker set has exactly 21 cells and is disjoint from the blocker's set after 20 rounds. Moreover, for every k < 21, the maker's and blocker's sets after k rounds are disjoint and the blocker's set has exactly k cells. The blocker's 21st reply is not constrained by the legality condition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyTwentyOne.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SnakyTwentyOne.lean; bytes 1586..2177
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SnakyTwentyOne

namespace OAI

namespace SnakyPrototype

open OrdinaryStrategy

theorem snaky_winning_strategy_21_with_legal_states :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 ∧
        (playState σ 21 β ∅ ∅ 21).1.card = 21 ∧
        Disjoint (playState σ 21 β ∅ ∅ 21).1 (playState σ 21 β ∅ ∅ 20).2 ∧
        ∀ k, k < 21 →
          Disjoint (playState σ 21 β ∅ ∅ k).1 (playState σ 21 β ∅ ∅ k).2 ∧
          (playState σ 21 β ∅ ∅ k).2.card = k := by
  sorry

end SnakyPrototype
end OAI
