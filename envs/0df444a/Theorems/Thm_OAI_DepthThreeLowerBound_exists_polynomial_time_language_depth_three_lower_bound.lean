-- Prove2me | Theorems.Thm_OAI_DepthThreeLowerBound_exists_polynomial_time_language_depth_three_lower_bound
-- name    : OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:33.991019+00:00
-- url     : https://prove2.me/theorems/ca5d3ba9-a9f6-4ccf-89f5-df5470b07771
-- statement:
--   The theorem states that there exist a Boolean-valued language L on finite lists of bits, a finite multi-tape Turing machine M, and positive natural numbers C and a such that M decides L in polynomial time, while L has no subexponential-in-√n depth-three circuits. Here M has finitely many tapes, one designated input tape, finite tape alphabet with a blank, and finitely many states, with two distinct non-blank symbols encoding the input bits. It starts in its initial state with the input word on the input tape and all other tapes empty, and each step reads all heads, then moves to a new state, writes a symbol on every tape and moves each head left, right or stays; the machine halts when no transition is defined, and its output is given by a Boolean acceptance predicate on the halting state. The polynomial-time condition says that for every bit list w, M halts on w within C(|w|+1)^a steps with output exactly L(w). The lower bound says that for every real A>0 there is N such that for all n≥N, every depth-three circuit D on the n Boolean variables indexed by Fin n that computes the restriction of L to length-n inputs (x is read as the list of its n bits) satisfies 2^(A√n) < gateCount(D). A depth-three circuit consists of bottom clauses, each an OR of literals or constants, middle gates, each an AND over a chosen set of bottom clauses, and one top gate, an OR over a chosen set of middle gates, with gateCount equal to bottom count plus middle count plus one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DepthThree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DepthThree.lean; bytes 3941..4417
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DepthThree

namespace OAI

namespace DepthThreeLowerBound

universe uV uS uK uGamma uQ

variable {V : Type uV}

attribute [instance] FiniteMultiTapeMachine.tapeFinite
  FiniteMultiTapeMachine.tapeDecidableEq FiniteMultiTapeMachine.alphabetInhabited
  FiniteMultiTapeMachine.alphabetFinite FiniteMultiTapeMachine.stateFinite

theorem exists_polynomial_time_language_depth_three_lower_bound :
    ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ),
      0 < C ∧ 0 < a ∧
      (∀ w : List Bool, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) →
          (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (D.gateCount : ℝ) := by
  sorry

end DepthThreeLowerBound
end OAI
