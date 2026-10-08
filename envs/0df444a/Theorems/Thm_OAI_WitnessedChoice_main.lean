-- Prove2me | Theorems.Thm_OAI_WitnessedChoice_main
-- name    : OAI.WitnessedChoice.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:39.467024+00:00
-- url     : https://prove2.me/theorems/a18f3289-111b-4a1a-8df6-69198c0f8487
-- statement:
--   The theorem states that the defined proposition BGS.MainStatement holds, i.e. there is a sentence φ of a set-theoretic logic over finite relational inputs that has exactly one witnessed-choice construct, always evaluates to a definite Boolean, and is not equivalent to any sentence with no such construct. An input is a finite carrier set A with a Boolean-valued binary relation on A for each symbol in a fixed list: Ed, Cf, EB, VB, I, and Z(δ) for each δ in ZMod 3. Terms denote hereditarily finite sets built over the atoms of A and may be variables, the empty set, the set of all atoms, pairs, unions, the unique element of a singleton, cardinalities (as von Neumann ordinals), set comprehensions with a range term and a guard formula, and an ordinary iteration of a step term. Formulas are equalities, input-relation atoms on atoms, negation, conjunction, disjunction, and the witnessed-choice formula, which has a step term, a choice term, a witness term and an output formula. Evaluation is partial: it returns none when a subterm is undefined, when the iteration or comprehension fails, or when the side conditions of a witnessed-choice formula fail, and otherwise returns a Boolean. Iterations run for a resource bound given by evaluating a real polynomial, attached to the sentence, at the carrier size and taking the floor. The witnessed-choice side conditions concern all chains of choices along the step iteration: chains that never repeat must have length at most the bound and bounded transitive closure, and each choice set must be nonempty with the step defined on all its elements. For the first repeating chain, witnesses must exist, consisting of sets of permutation graphs that are automorphisms of the input, fix the free parameters and the earlier states, and connect any two elements of each choice set. The output formula must then be defined at the final state, and the result is true exactly when it is true for all such final states. MainStatement asserts that there exist a formula φ with polynomial such that φ has exactly one witnessed-choice subformula, evaluates to some Boolean on every finite input, and for every sentence ψ containing no witnessed-choice constructs, the class of finite inputs on which φ evaluates to true differs from the class on which ψ evaluates to true.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WitnessedChoice.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WitnessedChoice.lean; bytes 17702..17780
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_WitnessedChoice

namespace OAI

noncomputable section

universe u v w

theorem WitnessedChoice.main : WitnessedChoice.BGS.MainStatement := by
  sorry

end
end OAI
