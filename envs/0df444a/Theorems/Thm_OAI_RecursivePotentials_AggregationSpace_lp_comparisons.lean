-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_AggregationSpace_lp_comparisons
-- name    : OAI.RecursivePotentials.AggregationSpace.lp_comparisons
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:24:38.634794+00:00
-- url     : https://prove2.me/theorems/59ade0b8-2c95-4744-a63c-452f4ad29088
-- title:
--   Two-sided $\ell^p$ comparison for the completed root-sum space of a tree of height at most $h$
-- statement:
--   Let $I$ be an arbitrary, possibly infinite, index set carrying a rooted tree $T$: a root $r$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth function $\operatorname{dep}:I\to\mathbb{N}$ with $\operatorname{dep}(r)=0$ and $\operatorname{dep}(\pi(s))<\operatorname{dep}(s)$ for $s\neq r$; a node may have infinitely many children. Fix a real exponent $p\ge1$.
--
--   For a finitely supported vector $v:I\to\mathbb{R}$ let its *head* $H(v)$ be the finite set consisting of $r$ and all ancestors of points of the support of $v$ (each point counting as its own ancestor). On the finite tree $H(v)$ the potentials are computed from the deepest nodes upwards by $P_s(v)=\max(A_s,\,v_s+B_s)$ and $Q_s(v)=\max(B_s,\,A_s-v_s)$, where $A_s=\bigl(\sum_c P_c(v)^p\bigr)^{1/p}$ and $B_s=\bigl(\sum_c Q_c(v)^p\bigr)^{1/p}$, the sums running over the children $c$ of $s$ inside $H(v)$; outside $H(v)$ they are set to $0$. The root sum $\|v\|=P_r(v)+Q_r(v)$ is a norm on the space $c_{00}(I)$ of finitely supported vectors, and $X_{T,p}$ denotes the completion of $(c_{00}(I),\|\cdot\|)$.
--
--   Assume now that $p>1$, that $\operatorname{dep}(c)=\operatorname{dep}(\pi(c))+1$ for every $c\neq r$, and that $\operatorname{dep}(s)\le h$ for every $s\in I$, for some $h\in\mathbb{N}$. Under these hypotheses the identity map of $c_{00}(I)$, regarded as a map into $\ell^p(I)$, extends to an isomorphism of Banach spaces $\Phi:X_{T,p}\to\ell^p(I)$, which sends each $x$ to the sequence of its coordinates. The theorem states that for every $x\in X_{T,p}$
--   $$
--   (h+1)^{-1/p}\,\|\Phi x\|_{\ell^p}\;\le\;\|x\|\;\le\;2\,(h+1)^{1-1/p}\,\|\Phi x\|_{\ell^p}.
--   $$
--
--   Thus on trees of bounded height the recursively defined root-sum norm is equivalent to the $\ell^p$ norm of the coordinates, with constants depending only on $h$ and $p$ and not on the branching of the tree. Through $\Phi$, properties of $\ell^p$ such as reflexivity and separability of the dual transfer to $X_{T,p}$. For the height-$h$ component trees with $p=1+1/h$, the two bounds are exactly the norm comparisons asserted for the root-sum functional $\nu$ on the $\ell^p$-coordinate model of the variable-exponent space.
--
--   **Formalization Note** $X_{T,p}$ is `AggregationSpace T e`, the `UniformSpace.Completion` of `AggregationVector T e` (finitely supported functions `ι →₀ ℝ` normed by `VariableTree.normSum`), and $\ell^p(I)$ is `lp (fun _ => ℝ) (ENNReal.ofReal e.val)`. The isomorphism $\Phi$ is `lpEquiv T e hp hstep h hh`; it is built from the coordinate embedding, its comparison bounds on finitely supported vectors and the density of finitely supported sequences, which is why its definition takes the hypotheses of the theorem as arguments. The index type only carries a `DecidableEq` instance, and `h` is a natural number, possibly $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableLp.lean#L293-L312

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.AggregationSpace
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology
open Filter Topology TopologicalSpace
open scoped ENNReal
open AggregationVector
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem OAI.RecursivePotentials.AggregationSpace.lp_comparisons (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (x : AggregationSpace T e) :
    (h+1:ℝ)^(-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ ≤ ‖x‖ ∧
      ‖x‖ ≤ 2*(h+1:ℝ)^(1-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ := by sorry
