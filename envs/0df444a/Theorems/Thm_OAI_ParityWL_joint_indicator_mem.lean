-- Prove2me | Theorems.Thm_OAI_ParityWL_joint_indicator_mem
-- name    : OAI.ParityWL.joint_indicator_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:04:23.77156+00:00
-- url     : https://prove2.me/theorems/9618524c-167e-405e-bc33-c99504134406
-- title:
--   Joint Weisfeiler–Leman color classes lie in the span of rooted test counts of bag size $t\ge k+1$
-- statement:
--   Let $G$ and $H$ be finite simple graphs with vertex sets $V$ and $W$, and let $k,t\in\mathbb N$ satisfy $k+1\le t$. All functions below are defined on the disjoint union $\mathcal X_k=V^k\sqcup W^k$ of the $k$-tuples of $G$ and the $k$-tuples of $H$; for $x\in\mathcal X_k$ write $\Gamma_x\in\{G,H\}$ for the graph that $x$ comes from and $U_x$ for its vertex set.
--
--   **Rooted tests.** A rooted test $F$ with $k$ roots and bag size $t$ consists of a finite set $A$ with a symmetric relation $R$ (loops allowed), roots $\rho_1,\dots,\rho_k\in A$ (not necessarily distinct), and a rooted tree decomposition of $(A,R)$ in which every pair related by $R$ lies in a common bag, the nodes whose bags contain a fixed element of $A$ form a subtree, every bag has at most $t$ elements, every non-root bag shares fewer than $t$ elements with the bag of its parent, and the root bag is exactly $\{\rho_1,\dots,\rho_k\}$. Its count at $x\in\mathcal X_k$ is
--   $$
--   \hom_F(x)=\#\bigl\{f:A\to U_x \;:\; f(a)f(b)\in E(\Gamma_x)\text{ whenever } aRb,\ \text{and } f(\rho_i)=x_i \text{ for } i=1,\dots,k\bigr\}.
--   $$
--   The test space $\mathcal S_{k,t}(G,H)\subseteq\mathbb Q^{\mathcal X_k}$ is the $\mathbb Q$-linear span of all functions $x\mapsto\hom_F(x)$, where $F$ ranges over rooted tests with $k$ roots and bag size $t$.
--
--   **Joint colors.** Let $\mathcal C_0$ be the set of $k\times k$ arrays with entries in $\{0,1\}^2$, and $\mathcal C_{r+1}=\mathcal C_r\times\mathcal M(\mathcal C_r^{\,k})$, where $\mathcal M(S)$ denotes the finite multisets over $S$. The round-$0$ color $c^0(x)\in\mathcal C_0$ is the atomic type of $x$: its $(i,j)$ entry records whether $x_i=x_j$ and whether $x_ix_j\in E(\Gamma_x)$. Inductively,
--   $$
--   c^{r+1}(x)=\Bigl(c^{r}(x),\ \bigl\{\!\!\bigl\{\bigl(c^{r}(x[1\mapsto v]),\dots,c^{r}(x[k\mapsto v])\bigr) : v\in U_x\bigr\}\!\!\bigr\}\Bigr)\in\mathcal C_{r+1},
--   $$
--   where $x[i\mapsto v]$ is $x$ with its $i$-th entry replaced by $v$. Tuples of $G$ and of $H$ are colored in the same sets $\mathcal C_r$, so their colors can be compared.
--
--   **Statement.** For every round $r\ge 0$ and every $d\in\mathcal C_r$, the indicator of the color class of $d$ lies in the test space:
--   $$
--   \mathbf 1[c^{r}=d]\in\mathcal S_{k,t}(G,H),\qquad\text{where}\quad \mathbf 1[c^{r}=d](x)=\begin{cases}1,& c^{r}(x)=d,\\ 0,&\text{otherwise.}\end{cases}
--   $$
--
--   Consequently, two finite families of tuples that receive the same total count from every rooted test with $k$ roots and bag size $t$ have the same multiset of joint colors at every round. The coloring $c^r$ is the joint (often called folklore) form of $k$-dimensional Weisfeiler–Leman refinement, and the case $t=k+1$ is what turns equality of homomorphism counts from tree-decomposed patterns into joint $k$-WL equivalence of the zero and star parity lifts, both for the two lifts themselves and for the pure comparison inside their disjoint union.
--
--   **Formalization Note** The tuple set is `TuplePair V W k`, i.e. `(Fin k → V) ⊕ (Fin k → W)`; the coloring is `pairJoint G H k r`, which applies `jointColor` on each summand; the span is the rational submodule `testSpan G H k t`, and tests are the structure `RootedTest k t`, whose tree is a `RankedBagTree` (the subtree condition is expressed through a highest node `top` containing each element together with convexity along ancestor chains). The color `d` ranges over the whole type `JointColor k r`, so colors realized by no tuple are allowed; their indicator is the zero function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/ColorSpan.lean#L109-L140

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
import Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

theorem OAI.ParityWL.joint_indicator_mem {k t : ℕ} (hkt : k + 1 ≤ t) (r : ℕ) (d : JointColor k r) :
    (fun x => if pairJoint G H k r x = d then (1 : ℚ) else 0) ∈ testSpan G H k t := by sorry
