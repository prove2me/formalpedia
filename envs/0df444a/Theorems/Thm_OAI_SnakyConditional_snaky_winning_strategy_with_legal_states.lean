-- Prove2me | Theorems.Thm_OAI_SnakyConditional_snaky_winning_strategy_with_legal_states
-- name    : OAI.SnakyConditional.snaky_winning_strategy_with_legal_states
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-07T04:33:23.613985+00:00
-- url     : https://prove2.me/theorems/ba8a045d-4e6e-478a-8e05-4c1527165825
-- statement:
--   The theorem states that there is a policy σ for a maker-breaker style game on the integer grid ℤ×ℤ, where a policy maps the number of remaining rounds, the maker's current finite set and the breaker's current finite set to a cell, such that σ always proposes a cell lying in neither set. Moreover, for every breaker reply sequence β from ℕ to cells that is legal before the final round, played for N=35 rounds from empty initial sets, several things hold. Here round k (counting from 0) has the maker add σ(35−k, M, B) to its set M and the breaker add β(k) to its set B, and legality means that for every k with k+1<35, β(k) is neither the maker's newly chosen cell, nor already in M, nor already in B. Under this assumption the maker's final set after 35 rounds contains a copy of the six-cell shape {(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)} under one of the eight rotations and reflections of the square lattice, followed by a translation; the final maker set has exactly 35 cells; it is disjoint from the breaker's set after 34 rounds; and for every k<35 the maker and breaker sets after k rounds are disjoint and the breaker set has exactly k cells.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyConditional.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SnakyConditional.lean; bytes 1454..2042
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SnakyConditional

namespace OAI.SnakyConditional

open OrdinaryStrategy

theorem snaky_winning_strategy_with_legal_states :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (playState σ 35 β ∅ ∅ 35).1 ∧
        (playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
        Disjoint (playState σ 35 β ∅ ∅ 35).1 (playState σ 35 β ∅ ∅ 34).2 ∧
        ∀ k, k < 35 →
          Disjoint (playState σ 35 β ∅ ∅ k).1 (playState σ 35 β ∅ ∅ k).2 ∧
          (playState σ 35 β ∅ ∅ k).2.card = k := by
  sorry

end OAI.SnakyConditional
