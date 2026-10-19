-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_inverse_offdiag_nonpos
-- name    : OAI.HyperedgeComparison.inverse_offdiag_nonpos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:08:47.334037+00:00
-- url     : https://prove2.me/theorems/dcacb419-dfed-4d09-9765-7338a5928591
-- title:
--   Off-diagonal entries of the inverse base matrix are nonpositive
-- statement:
--   Let $(H_e)_{e\in E}$ be a hypergraph on $V$ with finitely many labels, and let $\mathbb P_p$ be the product law of independent hyperedge states with $\mathbb P(\omega_e=1)=p_e$. Write $\mathcal C^\omega_D(x)$ for the cluster of $x$ using open hyperedges disjoint from $D$, and $\mathcal C^\omega_D(S)$ for the union over $x\in S$. The mean after deletion is $m_W(F)=\mathbb E_p\,F(\mathcal C_W(s))$. For listed vertices $x_1,\dots,x_n$, the first root of $x_i$ is the first $x_k$ whose cluster (no deletion) contains $x_i$ and avoids all earlier $x_j$, $j<k$. The column of an observable $F$ is $\mathrm{col}_k(F)_i=\mathbb E_p\bigl[\mathbf 1\{x_k\text{ is the first root of }x_i\}\,F(\mathcal C(x_k))\bigr]$, the base matrix is $B_{ik}=\mathrm{col}_k(\mathbf 1)_i$, and $\mathrm{coeff}_k(F)=B^{-1}\mathrm{col}_k(F)$. If all $p_e<1$ and the listed vertices are distinct, then for $i\ne k$,
--   $$
--   (B^{-1})_{ik}\le0 .
--   $$
--
--   So the base matrix is an inverse M-matrix type object.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L1294-L1323

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

theorem OAI.HyperedgeComparison.inverse_offdiag_nonpos [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) {k i : Fin n} (hik : i ≠ k) :
    (baseMatrix H p x)⁻¹ i k ≤ 0 := by sorry
