-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_coeff_identity
-- name    : OAI.HyperedgeComparison.coeff_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:07:39.419976+00:00
-- url     : https://prove2.me/theorems/03ec0700-e524-4d79-a5a2-6f0061fc4445
-- title:
--   Coefficient identity for resampled observables
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For listed vertices $x_1,\dots,x_n$, the first root of $x_i$ is the first $x_k$ whose cluster (no deletion) contains $x_i$ and avoids all earlier $x_j$, $j<k$. The column of an observable $F$ is $\mathrm{col}_k(F)_i=\mathbb E_p\bigl[\mathbf 1\{x_k\text{ is the first root of }x_i\}\,F(\mathcal C(x_k))\bigr]$, the base matrix is $B_{ik}=\mathrm{col}_k(\mathbf 1)_i$, and $\mathrm{coeff}_k(F)=B^{-1}\mathrm{col}_k(F)$. For a vertex $s$ and a set $S\not\ni s$, the resampling operator acts on observables $F$ of cluster domains $U$ ($s\in U$, $U\cap S=\varnothing$) by $\mathrm{res}(F)(U)=\mathbb E_\omega\bigl[m_{\mathcal C^\omega_U(S)}(F)\bigr]$: first sample the clusters of $S$ avoiding $U$, then the cluster of $s$ avoiding them. The residual mean is $\mathbb E_\omega\bigl[\mathbf 1\{s\notin\mathcal C^\omega_U(S)\}\,(m_{\mathcal C^\omega_U(S)}(F)-m_{\mathcal C^\omega_U(S)\cup U}(F))\bigr]$. For every $k$ and observable $F$, with $s=x_k$ and $S=\{x_l:l<k\}$,
--   $$
--   \mathrm{coeff}_k(F)=\mathrm{coeff}_k\bigl(\mathrm{res}(F)\bigr)+\sum_{j>k}\mathrm{coeff}_j\bigl(\mathrm{resid}(\cdot,F)\bigr).
--   $$
--
--   Resampling changes coefficients only through later columns.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L1123-L1138

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

theorem OAI.HyperedgeComparison.coeff_identity [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    coeff H p x k F = coeff H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then coeff H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by sorry
