-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_cluster_delete_clusters
-- name    : OAI.HyperedgeComparison.cluster_delete_clusters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:56:02.064441+00:00
-- url     : https://prove2.me/theorems/60e4c45b-c2fb-4d9e-b241-fa6c74368f06
-- title:
--   Deleting other clusters does not change a cluster
-- statement:
--   For a hypergraph $(H_e)_e$ on $V$ and a configuration $\omega$ of hyperedges, $\mathcal C_D(x)$ is the cluster of $x$ using open hyperedges disjoint from a deleted set $D$, and $\mathcal C_D(S)=\bigcup_{x\in S}\mathcal C_D(x)$. If $x\notin\mathcal C_D(S)$, then deleting the clusters of $S$ as well does not change the cluster of $x$:
--   $$
--   \mathcal C_{D\cup\mathcal C_D(S)}(x)=\mathcal C_D(x).
--   $$
--
--   This is the Markov property of clusters used in the resampling argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L110-L128

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}

theorem OAI.HyperedgeComparison.cluster_delete_clusters {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} (hx : x ∉ clusters H ω D S) :
    cluster H ω (D ∪ clusters H ω D S) x = cluster H ω D x := by sorry
