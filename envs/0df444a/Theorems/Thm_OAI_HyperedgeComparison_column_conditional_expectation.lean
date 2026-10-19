-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_column_conditional_expectation
-- name    : OAI.HyperedgeComparison.column_conditional_expectation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:03:20.634645+00:00
-- url     : https://prove2.me/theorems/ad06b917-e2ab-4641-83b2-63fc86bb1fc0
-- title:
--   Column entries integrate functions away from the cluster
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For listed vertices $x_1,\dots,x_n$, the first root of $x_i$ is the first $x_k$ whose cluster (no deletion) contains $x_i$ and avoids all earlier $x_j$, $j<k$. The column of an observable $F$ is $\mathrm{col}_k(F)_i=\mathbb E_p\bigl[\mathbf 1\{x_k\text{ is the first root of }x_i\}\,F(\mathcal C(x_k))\bigr]$, the base matrix is $B_{ik}=\mathrm{col}_k(\mathbf 1)_i$, and $\mathrm{coeff}_k(F)=B^{-1}\mathrm{col}_k(F)$. Let $g(\omega,U)$ depend, for fixed $U$, only on hyperedges disjoint from $U$. Then
--   $$
--   \mathbb E_\omega\bigl[\mathbf 1\{x_k\text{ first root of }x_i\}\,g(\omega,\mathcal C(x_k))\bigr]=\mathrm{col}_k\bigl(U\mapsto\mathbb E_{\omega'}g(\omega',U)\bigr)_i .
--   $$
--
--   Columns therefore commute with averaging over hyperedges away from the cluster.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L664-L688

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

theorem OAI.HyperedgeComparison.column_conditional_expectation [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, if firstRoot H x ω ∅ k i then g ω (cluster H ω ∅ (x k)) else 0 ∂law p) =
      column H p x k (fun U => ∫ ω, g ω U ∂law p) i := by sorry
