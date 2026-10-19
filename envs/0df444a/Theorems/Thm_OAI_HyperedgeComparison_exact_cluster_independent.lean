-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_exact_cluster_independent
-- name    : OAI.HyperedgeComparison.exact_cluster_independent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:59:09.555006+00:00
-- url     : https://prove2.me/theorems/d4d4be8a-0cad-4710-b0fb-29a9de439bc1
-- title:
--   The exact cluster event is independent of bits away from the cluster
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For sets $D,S,W\subseteq V$ and any $g$ that depends only on hyperedges disjoint from $W$, the indicator of the event $\{\mathcal C_D(S)=W\}$ is independent of $g$:
--   $$
--   \mathbf 1\{\mathcal C_D(S)=W\}\perp g .
--   $$
--
--   This is the spatial Markov property of percolation clusters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L365-L394

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

theorem OAI.HyperedgeComparison.exact_cluster_independent (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    IndepFun (fun ω => if clusters H ω D S = W then (1 : ℝ) else 0) g (law p) := by sorry
