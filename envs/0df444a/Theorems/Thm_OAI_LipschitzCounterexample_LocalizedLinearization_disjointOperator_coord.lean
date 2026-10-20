-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_disjointOperator_coord
-- name    : OAI.LipschitzCounterexample.LocalizedLinearization.disjointOperator_coord
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:29:49.241759+00:00
-- url     : https://prove2.me/theorems/f64b2452-d72e-4657-8b3e-78ed8e7acdb9
-- title:
--   Coordinates of the disjoint-test operator
-- statement:
--   Let $h_i:M\to\mathbb R$ be uniformly $K$-Lipschitz functions on a pointed metric space with disjoint supports, i.e. at most one $h_i$ is nonzero at each point. Let $\Theta:\mathcal F(M)\to\ell^1$ be the linearization of $x\mapsto h_{i(x)}(x)e_{i(x)}$, normalized at the base point. Then for every $\mu\in\mathcal F(M)$ and $i$,
--   $$
--   \Theta(\mu)_i=\bigl\langle\mu,\ h_i-h_i(0)\bigr\rangle .
--   $$
--
--   So each coordinate of the operator is the pairing with one normalized test function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/Localization.lean#L245-L259

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
universe uM uV
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem OAI.LipschitzCounterexample.LocalizedLinearization.disjointOperator_coord {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) (μ : FreeSpace.Space M) (i : ℕ) :
    disjointOperator hd μ i = test (normalized (h i) (hh i)) μ := by sorry
