-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_column_residual
-- name    : OAI.HyperedgeComparison.column_residual
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:04:23.429604+00:00
-- url     : https://prove2.me/theorems/0f4c715b-96d5-4a50-8ebd-af1feafb0407
-- title:
--   Columns of residual means
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For listed vertices $x_1,\dots,x_n$, the first root of $x_i$ is the first $x_k$ whose cluster (no deletion) contains $x_i$ and avoids all earlier $x_j$, $j<k$. The column of an observable $F$ is $\mathrm{col}_k(F)_i=\mathbb E_p\bigl[\mathbf 1\{x_k\text{ is the first root of }x_i\}\,F(\mathcal C(x_k))\bigr]$, the base matrix is $B_{ik}=\mathrm{col}_k(\mathbf 1)_i$, and $\mathrm{coeff}_k(F)=B^{-1}\mathrm{col}_k(F)$. For a vertex $s$ and a set $S\not\ni s$, the resampling operator acts on observables $F$ of cluster domains $U$ ($s\in U$, $U\cap S=\varnothing$) by $\mathrm{res}(F)(U)=\mathbb E_\omega\bigl[m_{\mathcal C^\omega_U(S)}(F)\bigr]$: first sample the clusters of $S$ avoiding $U$, then the cluster of $s$ avoiding them. The residual mean is $\mathbb E_\omega\bigl[\mathbf 1\{s\notin\mathcal C^\omega_U(S)\}\,(m_{\mathcal C^\omega_U(S)}(F)-m_{\mathcal C^\omega_U(S)\cup U}(F))\bigr]$. For $k<j$ and any observable $F$, the $j$-th column of the residual mean with $s=x_k$ and $S=\{x_l:l<k\}$, evaluated at $i$, equals
--   $$
--   \mathbb E\Bigl[\mathbf 1\{x_j\text{ first root of }x_i,\ x_k\notin\mathcal C(S)\}\bigl(m_{\mathcal C(S)}(F)-F(\mathcal C(x_k))\bigr)\Bigr].
--   $$
--
--   This expresses the residual terms of resampling through later columns.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L716-L750

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

theorem OAI.HyperedgeComparison.column_residual [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k j i : Fin n)
    (hkj : k < j) (F : Set V → ℝ) :
    column H p x j (residualMean H p (x k) (earlier x k) · F) i =
      ∫ ω, if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k) then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F -
          F (cluster H ω ∅ (x k)) else 0 ∂law p := by sorry
