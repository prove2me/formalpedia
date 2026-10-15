-- Prove2me | Theorems.Thm_OAI_DiscreteFree_projection_compact
-- name    : OAI.DiscreteFree.projection_compact
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:58:26.729188+00:00
-- url     : https://prove2.me/theorems/82b3b8be-141d-4dae-9cd7-d190e1f61636
-- title:
--   Finite-support projections converge to the identity uniformly on compact subsets of the free space
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ such that $d(x,y)\ge1$ whenever $x\ne y$, and let $B\ge0$ be such that $d(x,o)\le B$ for all $x\in M$. Let $\mathcal F(M)$ be the Lipschitz-free space of $(M,o)$: the closed linear span of the evaluation functionals $\delta(x):f\mapsto f(x)$ inside the dual of $\mathrm{Lip}_0(M)$, the space of real Lipschitz functions on $M$ vanishing at $o$ normed by their best Lipschitz constant. For $j\in M$ let $c_j(u)=\langle u,\chi_j\rangle$, where $\chi_j$ is the indicator of $\{j\}$ for $j\ne o$ and $\chi_o=0$, and for a finite set $G\subseteq M$ let $P_Gu=\sum_{j\in G}c_j(u)\,\delta(j)$ be the support projection.
--
--   **Theorem.** For every compact set $K\subseteq\mathcal F(M)$ and every $\varepsilon>0$ there is a finite set $F\subseteq M$ such that for every finite set $G$ with $F\subseteq G\subseteq M$,
--   $$
--   \|P_Gu-u\|<\varepsilon\qquad\text{for all }u\in K .
--   $$
--
--   In other words the net $(P_G)$, indexed by the finite subsets of $M$ ordered by inclusion, converges to the identity uniformly on compact sets. Together with the bound $\|P_G\|\le 2B$ this shows that $\mathcal F(M)$ has the bounded approximation property with constant $2B$; the theorem is also the tool for approximating a finite-rank operator $T$ in operator norm by $P_GT$.
--
--   **Formalization Note** The separation hypothesis is the variable `sep` used to build $P_G$ (`supportProjection o sep G`); the compact set is a `Set (FreeSpace o)` with `IsCompact`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/CompactApproximation.lean#L91-L114

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
variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)
variable (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)

include hB hb in
theorem OAI.DiscreteFree.projection_compact (C : Set (FreeSpace o)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ∀ u ∈ C,
      ‖supportProjection o sep G u - u‖ < ε := by sorry
