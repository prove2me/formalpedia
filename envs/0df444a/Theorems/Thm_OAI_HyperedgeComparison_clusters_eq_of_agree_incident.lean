-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_clusters_eq_of_agree_incident
-- name    : OAI.HyperedgeComparison.clusters_eq_of_agree_incident
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:56:35.365115+00:00
-- url     : https://prove2.me/theorems/4722036b-e006-47c3-ba77-0927fd5968dd
-- title:
--   Clusters depend only on hyperedges touching them
-- statement:
--   For a hypergraph $(H_e)_e$ on $V$ and a configuration $\omega$ of hyperedges, $\mathcal C_D(x)$ is the cluster of $x$ using open hyperedges disjoint from a deleted set $D$, and $\mathcal C_D(S)=\bigcup_{x\in S}\mathcal C_D(x)$. If two configurations $\omega,\omega'$ agree on every hyperedge that meets $\mathcal C^{\omega}_D(S)$, then
--   $$
--   \mathcal C^{\omega'}_D(S)=\mathcal C^{\omega}_D(S).
--   $$
--
--   The clusters of $S$ are determined by the states of the hyperedges incident to them.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L130-L161

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

theorem OAI.HyperedgeComparison.clusters_eq_of_agree_incident {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V}
    (hagree : ∀ e, ¬ Disjoint (H e) (clusters H ω D S) → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by sorry
