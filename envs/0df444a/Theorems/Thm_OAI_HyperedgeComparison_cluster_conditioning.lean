-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_cluster_conditioning
-- name    : OAI.HyperedgeComparison.cluster_conditioning
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:00:26.266317+00:00
-- url     : https://prove2.me/theorems/58dbe858-2fc4-4ad9-a0ad-2f10f053e0e7
-- title:
--   Conditioning on the exact clusters of a set
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For $s\notin W$ and any observable $F$,
--   $$
--   \mathbb E\bigl[\mathbf 1\{\mathcal C_D(S)=W\}\,F(\mathcal C_D(s))\bigr]=\mathbb P\bigl(\mathcal C_D(S)=W\bigr)\cdot m_{D\cup W}(F).
--   $$
--
--   Given the clusters of $S$, the cluster of an outside vertex is distributed as with those clusters deleted.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L540-L562

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
variable [Fintype E]

theorem OAI.HyperedgeComparison.cluster_conditioning (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S W : Set V) (F : Set V → ℝ)
    (hs : s ∉ W) :
    (∫ ω, if clusters H ω D S = W then F (cluster H ω D s) else 0 ∂law p) =
      clusterMass H p D S W * meanAfterDelete H p s (D ∪ W) F := by sorry
