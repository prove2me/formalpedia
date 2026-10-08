-- Prove2me | Theorems.Thm_OAI_MarkovSuperreflexivity_hasNontrivialMarkovType_iff_hasEquivalentUCNorm
-- name    : OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:54.806767+00:00
-- url     : https://prove2.me/theorems/bfe0496e-2d36-4ebd-a56d-7827cf4c584a
-- statement:
--   The theorem states that for a real normed space X that is complete (a Banach space), X has nontrivial Markov type if and only if X admits an equivalent uniformly convex norm. Nontrivial Markov type means there exist p>1 and K>0 such that for every finite reversible Markov chain on m states {0,…,m−1}, with stationary probability vector π, nonnegative row-stochastic transition matrix P, and detailed balance π(s)P(s,t)=π(t)P(t,s), every map f from the states to X, and every n≥1, the expected value of ‖f(Z_n)−f(Z_0)‖^p along n-step paths, started from π, is at most K^p·n times the corresponding one-step expectation of ‖f(Z_1)−f(Z_0)‖^p. Having an equivalent uniformly convex norm means there is a seminorm q on X and constants a,b>0 with a‖x‖≤q(x)≤b‖x‖ for all x, such that for every ε in (0,2] there is δ>0 with q((x+y)/2)≤1−δ whenever q(x)≤1, q(y)≤1 and q(x−y)≥ε.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MarkovType.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MarkovType.lean; bytes 2126..2271
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MarkovType

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasNontrivialMarkovType_iff_hasEquivalentUCNorm [CompleteSpace X] :
    HasNontrivialMarkovType X ↔ HasEquivalentUCNorm X := by
  sorry

end MarkovSuperreflexivity
end
end OAI
