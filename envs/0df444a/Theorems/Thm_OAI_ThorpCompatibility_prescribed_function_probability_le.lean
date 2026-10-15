-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_prescribed_function_probability_le
-- name    : OAI.ThorpCompatibility.prescribed_function_probability_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:57:39.139956+00:00
-- url     : https://prove2.me/theorems/c3779875-06cd-4fd8-94c4-8b852e90b310
-- title:
--   A uniform permutation agrees with a prescribed map on a set $s$ with probability at most $(e/n)^{|s|}$
-- statement:
--   Let $X$ be a finite set with $n=|X|\ge1$ elements, let $s\subseteq X$, and let $f:X\to X$ be an arbitrary map. For a uniformly random permutation $\tau$ of $X$, the probability that $\tau$ agrees with $f$ at every point of $s$ is at most $(e/n)^{|s|}$:
--   $$
--   \frac{\big|\{\tau\in S_X:\ \tau(x)=f(x)\ \text{for all }x\in s\}\big|}{n!}\le\Big(\frac{e}{n}\Big)^{|s|}.
--   $$
--
--   Prescribing the values of a uniform permutation at $|s|$ points costs a factor of order $1/n$ per point. When $f$ is injective on $s$ the exact probability is $(n-|s|)!/n!$, and the bound replaces it by a clean geometric expression. This is the one-row ingredient in bounding the probability that independent uniform row permutations meet prescribed cell lists, and hence the exponential moment of the clump count.
--
--   **Formalization Note** $X$ is a `Fintype` with decidable equality and $s$ is a `Finset`; the left side is the cardinality of a filtered `Finset` of `Equiv.Perm α` divided by `Fintype.card (Equiv.Perm α)`. The map $f$ need not be injective; if no permutation agrees with $f$ on $s$, the left side is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/PermutationProbability.lean#L12-L36

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem OAI.ThorpCompatibility.prescribed_function_probability_le {α : Type*} [Fintype α] [DecidableEq α]
    (hn : 0 < Fintype.card α) (s : Finset α) (f : α → α) :
    ((Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ (Real.exp 1 / Fintype.card α) ^ s.card := by sorry
