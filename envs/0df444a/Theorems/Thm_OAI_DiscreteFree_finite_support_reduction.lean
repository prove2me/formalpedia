-- Prove2me | Theorems.Thm_OAI_DiscreteFree_finite_support_reduction
-- name    : OAI.DiscreteFree.finite_support_reduction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:59:01.621209+00:00
-- url     : https://prove2.me/theorems/2849de46-56ae-4b08-afbb-51e7d9074991
-- title:
--   Finite-rank operators on the free space of a bounded discrete space can be compressed to finitely many coordinates
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ such that $d(x,y)\ge1$ whenever $x\ne y$. Let $\mathcal F(M)$ be its Lipschitz-free space, the closed linear span of the evaluation functionals $\delta(x):f\mapsto f(x)$, $x\in M$, in the dual of the space $\mathrm{Lip}_0(M)$ of real Lipschitz functions vanishing at $o$ (normed by the best Lipschitz constant). For a finite set $S\subseteq M$ let $P_Su=\sum_{j\in S}c_j(u)\,\delta(j)$ be the support projection, where $c_j(u)=\langle u,\chi_j\rangle$ and $\chi_j$ is the indicator of $\{j\}$ for $j\ne o$, $\chi_o=0$. An operator has *finite rank* if its range is finite-dimensional.
--
--   **Theorem.** Let $B\ge0$ and $p\ge1$ be real numbers with $d(x,o)\le B$ for every $x\in M$, let $A\subseteq M$ be finite, and let $T_0$ be a bounded linear operator on $\mathcal F(M)$ of finite rank such that $\|T_0\|\le p$ and $\|T_0\delta(a)-\delta(a)\|<\tfrac12$ for every $a\in A$. Then there exist a finite set $S\subseteq M$ with $o\in S$ and a bounded linear operator $T$ on $\mathcal F(M)$ of finite rank such that
--   $$
--   \|T\|\le 2p,\qquad P_S(Tu)=Tu\ \text{ for all }u\in\mathcal F(M),\qquad \|T\delta(a)-\delta(a)\|<1\ \text{ for all }a\in A .
--   $$
--
--   So, at the cost of doubling both the norm bound and the tolerance on the finite set $A$, one may assume that the range of the operator consists of finitely supported elements $\sum_{j\in S}t_j\,\delta(j)$. Every vector $T\delta(x)$ is then described by finitely many real coefficients, which is the starting point of the combinatorial obstruction showing that no finite-rank operator of norm at most $p$ can move all points of a suitable finite set $A$ by less than $\tfrac12$.
--
--   **Formalization Note** Finite rank is `Module.Finite ℝ (LinearMap.range T.toLinearMap)`. The separation hypothesis is the variable `sep` used to define $P_S$ (`supportProjection o sep S`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/SupportReduction.lean#L60-L97

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem OAI.DiscreteFree.finite_support_reduction (B p : ℝ) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hb : ∀ x, dist x o ≤ B) (A : Finset M)
    (T₀ : FreeSpace o →L[ℝ] FreeSpace o)
    (hfinite : Module.Finite ℝ (LinearMap.range T₀.toLinearMap)) (hnorm : ‖T₀‖ ≤ p)
    (hanchor : ∀ a ∈ A, ‖T₀ (delta o a) - delta o a‖ < 1/2) :
    ∃ (S : Finset M) (T : FreeSpace o →L[ℝ] FreeSpace o), o ∈ S ∧
      Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧ ‖T‖ ≤ 2*p ∧
      (∀ u, supportProjection o sep S (T u) = T u) ∧
      ∀ a ∈ A, ‖T (delta o a) - delta o a‖ < 1 := by sorry
