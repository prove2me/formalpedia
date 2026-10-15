-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_meetsLists_probability_le
-- name    : OAI.ThorpCompatibility.meetsLists_probability_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:58:16.576195+00:00
-- url     : https://prove2.me/theorems/e86bb6a0-27c4-4a0b-9c16-937c5d4a958d
-- title:
--   Uniform row permutations meet prescribed cell lists with probability at most $(e/n)$ per listed incidence
-- statement:
--   Let $I$ and $J$ be finite sets with $n=|J|\ge1$. A *list system* $S$ assigns to every cell $(j,k)\in J\times J$ a set $S(j,k)\subseteq I$ of rows. A family $r=(r_i)_{i\in I}$ of permutations of $J$ *meets the lists* if every row listed at a cell $(j,k)$ sends $j$ to $k$:
--   $$
--   i\in S(j,k)\ \Longrightarrow\ r_i(j)=k\qquad\text{for all }j,k\in J\text{ and }i\in I .
--   $$
--   If $r$ is chosen uniformly from $(S_J)^I$ (independent uniform permutations, one for each row), then
--   $$
--   \Pr_r\big[r\text{ meets the lists }S\big]\le\Big(\frac{e}{n}\Big)^{\sum_{(j,k)\in J\times J}|S(j,k)|}.
--   $$
--
--   Each listed incidence costs a factor $e/n$, as if the incidences were independent events of probability about $1/n$. The exponential moment of the clump count expands into a weighted sum over list systems of exactly these probabilities, so the bound turns that moment into a product of one-cell sums.
--
--   **Formalization Note** The probability is `uniformProbability (MeetsLists S)`: the number of families `r : α → Equiv.Perm β` with `MeetsLists S r` divided by the number of all such families. The row set $I$ may be empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ListIncidence.lean#L50-L82

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
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem OAI.ThorpCompatibility.meetsLists_probability_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hn : 0 < Fintype.card β)
    (S : β × β → Finset α) :
    uniformProbability (MeetsLists S) ≤
      (Real.exp 1 / Fintype.card β) ^ (∑ b, (S b).card) := by sorry
