-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_wsc_sumL1
-- name    : OAI.LipschitzCounterexample.WeakSequences.wsc_sumL1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:27:50.57479+00:00
-- url     : https://prove2.me/theorems/0a67d86f-2264-475c-a3bc-215582f87aba
-- title:
--   ℓ¹-sums of weakly sequentially complete spaces are weakly sequentially complete
-- statement:
--   Let $G_i$ be real normed spaces, each weakly sequentially complete: every weakly Cauchy sequence converges weakly. Then their $\ell^1$-sum
--   $$
--   \Bigl(\bigoplus_iG_i\Bigr)_{\ell^1}
--   $$
--   is weakly sequentially complete.
--
--   In particular $\ell^1$-sums of reflexive spaces, or of copies of a weakly sequentially complete space, are weakly sequentially complete.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean#L270-L327

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

theorem OAI.LipschitzCounterexample.WeakSequences.wsc_sumL1 (hG : ∀ i, WeakSequentiallyComplete (G i)) :
    WeakSequentiallyComplete (SumL1 G) := by sorry
