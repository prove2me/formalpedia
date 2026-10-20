-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_uniform_tails_of_weakCauchy
-- name    : OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_weakCauchy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:27:20.165062+00:00
-- url     : https://prove2.me/theorems/ef11306c-33ec-496f-afe5-00c6fbb40256
-- title:
--   Weakly Cauchy sequences in ℓ¹-sums have uniformly small tails
-- statement:
--   Let $u_k$ be a weakly Cauchy sequence in an $\ell^1$-sum $\bigl(\bigoplus_iG_i\bigr)_{\ell^1}$ of real normed spaces, i.e. $(f(u_k))_k$ is Cauchy for every bounded functional $f$. Then for every $\varepsilon>0$ there is $N$ with
--   $$
--   \sum_{i\ge N}\|u_k(i)\|<\varepsilon\quad\text{for all }k .
--   $$
--
--   So weak Cauchyness already forces uniform tail control.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean#L178-L252

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

theorem OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_weakCauchy (u : ℕ → SumL1 G) (hu : WeakCauchy u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by sorry
