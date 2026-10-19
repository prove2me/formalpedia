-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_resample_tendsto_constant
-- name    : OAI.HyperedgeComparison.resample_tendsto_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:05:33.782336+00:00
-- url     : https://prove2.me/theorems/be9dc4fd-9ecb-4217-a84a-ed53744026a1
-- title:
--   Iterated resampling converges to a constant
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For a vertex $s$ and a set $S\not\ni s$, the resampling operator acts on observables $F$ of cluster domains $U$ ($s\in U$, $U\cap S=\varnothing$) by $\mathrm{res}(F)(U)=\mathbb E_\omega\bigl[m_{\mathcal C^\omega_U(S)}(F)\bigr]$: first sample the clusters of $S$ avoiding $U$, then the cluster of $s$ avoiding them. The residual mean is $\mathbb E_\omega\bigl[\mathbf 1\{s\notin\mathcal C^\omega_U(S)\}\,(m_{\mathcal C^\omega_U(S)}(F)-m_{\mathcal C^\omega_U(S)\cup U}(F))\bigr]$. If all $p_e<1$, $s\notin S$, and $F\ge0$ on cluster domains, then there is $c\ge0$ such that for every domain $U$,
--   $$
--   \mathrm{res}^n(F)(U)\to c\quad(n\to\infty).
--   $$
--
--   The limit constant does not depend on the starting domain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L984-L1014

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

theorem OAI.HyperedgeComparison.resample_tendsto_constant [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (s : V) (S : Set V) (hs : s ∉ S) (F : Set V → ℝ)
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ U ∈ ClusterDomain s S,
      Tendsto (fun n : ℕ => ((resample H p s S)^[n] F) U) atTop (nhds c) := by sorry
