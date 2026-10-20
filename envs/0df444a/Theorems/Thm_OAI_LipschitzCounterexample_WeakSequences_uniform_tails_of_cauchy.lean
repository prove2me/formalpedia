-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_uniform_tails_of_cauchy
-- name    : OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_cauchy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:26:52.990037+00:00
-- url     : https://prove2.me/theorems/f9706e4e-0119-46af-ada8-2c4a8a197371
-- title:
--   Norm Cauchy sequences in ℓ¹-sums have uniformly small tails
-- statement:
--   Let $u_k$ be a norm Cauchy sequence in an $\ell^1$-sum $\bigl(\bigoplus_iG_i\bigr)_{\ell^1}$ of normed spaces. Then for every $\varepsilon>0$ there is $N$ such that
--   $$
--   \sum_{i\ge N}\|u_k(i)\|<\varepsilon\quad\text{for all }k .
--   $$
--
--   Uniform smallness of tails is the compactness ingredient used for $\ell^1$-sums.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean#L133-L152

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE uF uG
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

theorem OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_cauchy (u : ℕ → SumL1 G) (hu : CauchySeq u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by sorry
