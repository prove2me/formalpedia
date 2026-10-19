-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_resamplingTransition_atom
-- name    : OAI.HyperedgeComparison.resamplingTransition_atom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:04:57.432203+00:00
-- url     : https://prove2.me/theorems/9b329104-e5a2-4567-b96a-06602fb7df3b
-- title:
--   The resampling chain has a common atom
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For $s\notin S$ and every cluster domain $U$ ($s\in U$, $U\cap S=\varnothing$), the two-stage resampling transition moves to the singleton domain $\{s\}$ with probability at least the probability that all hyperedges are closed:
--   $$
--   K(U,\{s\})\ge\mathbb P_p(\omega\equiv0).
--   $$
--
--   This common atom drives the convergence of iterated resampling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L956-L982

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

theorem OAI.HyperedgeComparison.resamplingTransition_atom [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (hs : s ∉ S)
    (U : ClusterDomain s S) :
    (law p).real {fun _ => false} ≤ (resamplingTransition H p s S).weight U
      ⟨{s}, ⟨by simp, by simpa using hs⟩⟩ := by sorry
