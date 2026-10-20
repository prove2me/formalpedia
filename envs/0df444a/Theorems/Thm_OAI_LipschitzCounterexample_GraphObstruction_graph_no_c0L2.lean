-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_GraphObstruction_graph_no_c0L2
-- name    : OAI.LipschitzCounterexample.GraphObstruction.graph_no_c0L2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:29:10.902436+00:00
-- url     : https://prove2.me/theorems/6de9a267-7815-4993-9670-647415fc5443
-- title:
--   Weighted graph spaces of completely continuous operators contain no copy of c₀ of ℓ²
-- statement:
--   Let $Q:A\to H$ be a bounded operator from a weakly sequentially complete Banach space $A$, and assume $Q$ is completely continuous (it maps weakly null sequences to norm null ones). Then the weighted graph space $\mathcal G(Q)$ contains no isomorphic copy of $c_0(\ell^2)$. That is, there is no bounded operator $S:c_0(\ell^2)\to\mathcal G(Q)$ and $b>0$ with
--   $$
--   b\|x\|\le\|Sx\|\quad\text{for all }x .
--   $$
--
--   This is the space $Y$ side of the main counterexample.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/GraphObstruction.lean#L269-L328

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.GraphObstruction
universe uH uA uB
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
open NullSequences
variable {A : Type uA} {B : Type uB} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [CompleteSpace A] [CompleteSpace H]

omit [CompleteSpace H] in
theorem OAI.LipschitzCounterexample.GraphObstruction.graph_no_c0L2 (Q : A →L[ℝ] H) (hA : WeakSequentiallyComplete A)
    (hQ : CompletelyContinuous Q) (S : C0 (H := RealL2) →L[ℝ] WeightedGraph.Space Q)
    (b : ℝ) (hb : 0 < b) (hS : ∀ x, b * ‖x‖ ≤ ‖S x‖) : False := by sorry
