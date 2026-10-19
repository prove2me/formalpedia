-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_residualMean_eq_integral
-- name    : OAI.HyperedgeComparison.residualMean_eq_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:59:47.456622+00:00
-- url     : https://prove2.me/theorems/450cdcf1-a9f6-4571-a909-abb27d8cfcd0
-- title:
--   The residual mean as an expectation of a residual sample
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For a vertex $s$ and a set $S\not\ni s$, the resampling operator acts on observables $F$ of cluster domains $U$ ($s\in U$, $U\cap S=\varnothing$) by $\mathrm{res}(F)(U)=\mathbb E_\omega\bigl[m_{\mathcal C^\omega_U(S)}(F)\bigr]$: first sample the clusters of $S$ avoiding $U$, then the cluster of $s$ avoiding them. The residual mean is $\mathbb E_\omega\bigl[\mathbf 1\{s\notin\mathcal C^\omega_U(S)\}\,(m_{\mathcal C^\omega_U(S)}(F)-m_{\mathcal C^\omega_U(S)\cup U}(F))\bigr]$. The residual mean equals the expectation of the residual sample:
--   $$
--   \mathrm{resid}(U)=\mathbb E_\omega\Bigl[\mathbf 1\{s\notin\mathcal C_U(S)\}\bigl(F(\mathcal C_{\mathcal C_U(S)}(s))-F(\mathcal C_{\mathcal C_U(S)\cup U}(s))\bigr)\Bigr].
--   $$
--
--   So averages of the cluster of $s$ over independent copies can be replaced by the same configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L435-L483

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

theorem OAI.HyperedgeComparison.residualMean_eq_integral [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F = ∫ ω, residualSample H ω s S U F ∂law p := by sorry
